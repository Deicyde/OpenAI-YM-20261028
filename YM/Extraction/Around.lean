import YM.Cells.Embedded
import YM.Cells.OnGrid
import YM.Cells.Slide
import YM.Extraction.Center



/-!
# Uncentered bounds by reflecting whole arrays at a finer scale

No losing track of locations through orientation copies. .
Cost at each transformed label. Eventual margin fit separate. Standalone
publication of this logic for weak tasks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extraction
open Function Set Filter MeasureTheory Lattice Wilson Cells
open scoped Topology BigOperators ComplexOrder Matrix.Norms.Frobenius

namespace Spin
variable {G : Gauge} (L : Register G)
abbrev Frame := Signed × Bool
def token (x : L.Token) (p : Frame) := if p.2 then L.conjugate (L.move p.1 x) else L.move p.1 x
@[simp] lemma stay (v : L.Token) (p : Frame) : (token L v p).1 = v.1 := by unfold token;split <;> rfl
@[simp] lemma choose_id (x : L.Token) : token L x (1,false)=x := by simp [token,Register.move]
@[simp] lemma move_adds (x : L.Token) (s t) : L.move (t*s) x = L.move t (L.move s x) := by simp [Register.move];rfl
@[simp] lemma move_one (x : L.Token) : L.move 1 x=x := by simp [Register.move]
@[simp] lemma conjugate_twice (x : L.Token) : L.conjugate (L.conjugate x)=x := by
  rcases x with ⟨n,v⟩; change Sigma.mk _ (star (star v)) = _; rw [star_star]
@[simp] lemma swapC (x : L.Token) (s : Signed) : L.move s (L.conjugate x)=L.conjugate (L.move s x) := by
  rcases x with ⟨n,v⟩; change Sigma.mk n (L.mirrorGroup n s (star v)) = _
  exact congr_arg (fun y => (⟨n,y⟩ : L.Token)) (L.star_mirror s n v).symm

lemma orientation (x : L.Token) (p q : Frame) : token L (token L x p) q=token L x (q.1*p.1,p.2.xor q.2) := by rcases p with ⟨p,h|h⟩ <;> rcases q with ⟨q,h|h⟩ <;> simp [token]
@[simp] lemma isotropy (x : L.Token) (p : Frame) : token L (token L x (p.1⁻¹,p.2)) p=x := by rcases p with ⟨p,h|h⟩ <;> rw [orientation] <;> simp

variable {C : Family G} {N p k : ℕ}
open scoped Classical in
def way {n : Side} (T : Tiling n) (v : T.Cell) : Frame := (T.omega v,decide (T.hand v))

lemma uses (H : C.Makes) (T : Tiling (C.side N p)) (v : T.Cell) (x) (S : C.book.Token) (h : C.ref S.1 ≤ N) :
    T.copy v (C.seen S x) = C.seen (token C.book S (way T v)) (T.copyMap v x) := by
  classical
  funext U
  have he : C.seen (C.book.move (T.omega v) S) (T.copyMap v x) U=C.seen S x
      (pull (T.omega v) (T.translateBy v) U) := C.rotated H h ..
  by_cases hv : T.hand v
  · simp only [Tiling.copy,way,hv, decide_true, ↓reduceIte,token]; rw [← he]; exact (C.reality H h ..).symm
  simp only [Tiling.copy,way,hv, decide_false, ↓reduceIte,Bool.false_eq_true,token]; exact he.symm
end Spin
open Spin
namespace Around
variable {G : Gauge} {C : Family G} {N k p : ℕ}
variable (X : Tiling (C.side N p)) (u : C.book.Token)

lemma swept {o : Site (C.side N p)} (Hm : C.Makes) (hx : o∈X.chamber 0) (h : k ≤ N)
    (H : o∈onCenters C.S h (homeFor C.S h X))
    (he : Cells.span C.S h p ∣ X.side.val) (A : ℝ)
    (hc : ∀ b : Frame, centeredBudget C (token C.book u b) A k N p) :
    X.rootTest (C.beta N p) (C.seen u o) ≤ A := by
  set v := homeFor C.S h X
  let V := center C.S p h v
  let x (i : X.Cell) := X.copyMap i o
  choose f hf using fun i => show ∃ j : V.Cell, x i= V.copyMap j v from turns C.S h X H he i
  have hm : Injective f := by
    intro i j hp
    have ht := X.enumerate i hx
    have hs := X.enumerate j hx
    rw [show X.copyMap i o=X.copyMap j o from (hf i).trans (hp ▸ (hf j).symm)] at ht
    exact (X.which_chamber ht).symm.trans (X.which_chamber hs)
  let Z (i) := (way V (f i))
  let W (i) := token C.book u (way X i)
  let B (i) := token C.book (W i) ((Z i).1⁻¹,(Z i).2)
  have ht i : token C.book (B i) (way V (f i)) = W i := isotropy ..
  have hh i := hc (((Z i).1⁻¹ * (way X i).1),(way X i).2.xor (Z i).2)
  have he i : centeredBudget C (B i) A k N p := by dsimp only [B,W]; rw [orientation]; exact hh i
  let β := C.beta N p
  have hr i : C.ref (B i).1 ≤ N ∧ Interior (V.chamber 0) (C.seen (B i) v) ∧ V.rootTest β (C.seen (B i) v) ≤ A := by
    obtain ⟨ha,t,hb⟩ := he i
    exact ⟨t,hb v⟩
  have hx' : ∀ i, (B i).1=u.1 := by intro;simp [B,W]
  have Hs : C.ref u.1 ≤ N := hx' 0 ▸ (hr 0).1
  let F (i : X.Cell) := C.seen (B i) v
  have hp i : X.copy i (C.seen u o)=V.copy (f i) (F i) := by unfold F;rw [Spin.uses Hm X i _ _ Hs,
    Spin.uses Hm V (f i) v _ ((hr i).1),ht,show X.copyMap i o=V.copyMap (f i) v from hf i]
  have hn := (V.planted (seamless Hm ..) f hm F (fun i => (hr i).2.1)).trans
    (Finset.prod_le_prod (fun i _ => V.root_nonneg β _) fun i _ => (hr i).2.2)
  have hD := hn
  simp only [← hp, Finset.prod_const,Finset.card_univ] at hD
  haveI : Nonempty X.Cell := ⟨0⟩
  apply le_of_pow_le_pow_left₀ (Fintype.card_pos (α := X.Cell)).ne' ((V.root_nonneg β _).trans ((hr 0).2.2))
  rw [Tiling.powering]; exact hD

lemma interior_from (Hm : C.Makes) (h : k ≤ N) (he : Cells.span C.S h p ∣ X.side.val) (A : ℝ)
    (hc : ∀ b : Frame, centeredBudget C (token C.book u b) A k N p)
    (hs : ∀ o∈X.margin 0 (2 * Cells.span C.S h p), Interior (X.chamber 0) (C.seen u o))
    (o) (H : o∈X.margin 0 (3*Cells.span C.S h p)) : X.rootTest (C.beta N p) (C.seen u o) ≤ A := by
  classical
  let d := Cells.span C.S h p
  choose v j hj hv hr hz hx hg ha using fun i : Axis => bracket C.S h X o H i
  let Q (w : Axis → ℕ) i := v i (w i) i
  have ht w (hw : ∀ i, w i ≤ d) : Q w∈X.margin 0 (2*d) := by
    refine ⟨fun a => (hr a _ (hw a)).1 a,?_⟩
    intro i; exact (hr i _ (hw i)).2 i
  have hp (p : Axis → ℕ) (i : Axis) (l : ℕ) (hl : l+1 ≤ d) : Q (update p i (l+1)) = Q (update p i l) + step i := by
    funext b; by_cases he : b=i <;> simp [Q,he,hz i l hl]
  let S (q : Axis → ℕ) := X.rootTest (C.beta N p) (C.seen u (Q q))
  have hb (D : Finset Axis) (w : Axis → ℕ) (hw : ∀ i, w i ≤ d) (hR : ∀ i∉D, w i=0 ∨ w i=d) : S w ≤ A := by
    induction D using Finset.induction_on generalizing w with
    | empty =>
      apply swept X u Hm (ht w hw).1 h _ he A hc
      rw [belongs]; intro i
      rcases hR i (by simp) with e|e <;> unfold Q <;> rw [e]
      exacts [hg i, ha i]
    | @insert i D hi ih =>
      let W (x) := update w i x
      let F (x : ℕ) := C.seen u (Q (W x))
      have HH (x) (h : x ≤ d) : ∀ k, W x k ≤ d := fun k => by by_cases he:k=i <;> simp [W,he,hw,h]
      have he (x : ℕ) (h : x=0 ∨ x=d) (t) (ht:t∉D) : W x t=0 ∨ W x t=d := by
        by_cases hf:t=i; subst t;simpa [W]
        simpa [W,hf] using hR t (by simp [hf,ht])
      have hx' := X.pathway (C.beta N _) (seamless Hm ..) F d i (fun x hx => hs _ (ht _ (HH _ hx)))
        (fun x hx => ?_) A (ih _ (HH _ (Nat.zero_le _)) (he _ (Or.inl rfl))) (ih _ (HH d le_rfl) (he _ (Or.inr rfl)))
        _ (hw i)
      · change S (update w i (w i))≤A at hx'; simpa using hx'
      funext U; unfold F W; rw [hp w i x hx]; exact (C.translation ..).symm
  suffices he : o=Q j from he ▸ hb Finset.univ _ hj (by simp)
  ext i; simp [Q,hv]
end Around
end YM.Extraction
