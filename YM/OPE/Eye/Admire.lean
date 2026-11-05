import YM.OPE.Eye.Fleeting
/-!
# Swept estimate in a configuration at cutoff
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Lattice Cells Wilson Extraction Word
open Cards Bid Spec
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G:Gauge}{C:Family G}{F : Extraction.Order}{S:Table C.book} (U: Final C F S)(h:Org.Grill C F)
variable {I J : Type}[Fintype I][Fintype J] {N p k f b l n q : ℕ}
variable {𝓕 : Filter (ℕ×ℕ)}
variable {B:I→ℝ}{D:J→ℝ} {x:I→ Cover}{v:I→ C.book.Token}{y:J→ Cover}{w:J→ C.book.Token}
    (Z:ReadLabel C v)(Y:ReadLabel C w)

def combine : ReadLabel C (beside v w) := fun i=> match i with
    | .inl j=> Z j
    | .inr j=> Y j

lemma works (k N p:ℕ)(x:I→ Cover)(y:J→ Cover): register C k (beside x y) (germ (combine Z Y)) N p = register C k x (germ Z) N p * register C k y (germ Y) N p:= by
    funext U; unfold register; rw [Fintype.prod_sum_type]; rfl
include h
local notation "T'"=> C.S.gridPoint k
lemma admiring (hk:b ≤ k) (hh: Gap C.S k x (2*C.S.a b))(hp:Gap C.S k y (2*C.S.a l))(hd:GapTo C.S k x y (2*C.S.a b))
    (hX: Screen (beside ((T') ∘ x) ((T') ∘ y)))(he:Hall C.S b l q f n (Fintype.card I) (Fintype.card J))
    (hB:∀ j, ∀ᶠ i:ℕ×ℕ in F.fuse,PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) (B j) (C.O i.1 i.2 (d:=(v j).1) (v j).2 0))
    (hD:∀ j, ∀ᶠ i:ℕ×ℕ in F.fuse,PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (C.O i.1 i.2 (d:=(w j).1) (w j).2 0)) :
    ‖viewing U (beside ((T') ∘ x) ((T') ∘ y)) (beside v w)‖ ≤ (∏ i,B i)*∏ j,D j:=by
    let X:= frozen C v; let Z:= frozen C w; rw [← beside_commutes] at hX ⊢
    have hu(j): Tendsto (combine X Z j) F.fuse (𝓝 ((beside v w j).2)):=by cases j <;> exact tendsto_const_nhds
    exact TileDoc.global U (TileDoc.one U hX hu) h hk le_rfl hh hp hd he (z:= germ X) (w:= germ Z) hB hD (Eventually.of_forall fun i=>works X Z k i.1 i.2 x y)

-- translate and unit singleton cost
omit h in
lemma location_origin : location C.S k N p 0=0:=by
    unfold location; split; · rw [map_zero]; exact Ratio.root _|>.map_zero
    rfl
omit h in
lemma just_one (x: Cylinder C)(k N p:ℕ): register C k (fun _ : Unit => 0) (fun _=>x) N p=x N p:=by funext u; unfold register; simp [location_origin,-Order.fused]; rw [← pull_one,pull_id]

variable {t:ℕ}{P: ℕ×ℕ→ C.label t}{a:C.label t}(o:ℝ)
local notation "T0"=> (germ (frozen C v))
local notation "Z0"=> (fun _ : Unit=> (0:Cover))
omit h in
lemma grid_zero (S:Schedule)(t:ℕ): S.gridPoint t 0=0:=by ext; simp [Schedule.gridPoint]
lemma mirrorMatch (hk:b ≤ k)(hp:Gap C.S k y (2*C.S.a l))(hd:GapTo C.S k (Z0) y (2*C.S.a b))
    (hf:Screen (beside ((T') ∘ x) ((T') ∘ y)))
    (hx:Screen (beside ((T') ∘ Z0) ((T') ∘ y)))
    (he:Hall C.S b l q f n 1 (Fintype.card J)) [𝓕.NeBot] (hr:𝓕≤ F.fuse)(hz:Tendsto P 𝓕 (𝓝 a))
    (hB : ∀ᶠ i:ℕ×ℕ in 𝓕, PaidAt C.S i.1 i.2 q (C.beta i.1 i.2) o (register C k x (germ (frozen C v)) i.1 i.2 - C.O i.1 i.2 (P i) 0))
    (hD:∀ j, ∀ᶠ i:ℕ×ℕ in F.fuse,PaidAt C.S i.1 i.2 n (C.beta i.1 i.2) (D j) (C.O i.1 i.2 (d:=(w j).1) (w j).2 0)) :
    ‖viewing U (beside ((T') ∘ x) ((T') ∘ y)) (beside v w) - viewing U (beside ((T') ∘ Z0) ((T') ∘ y)) (beside (fun _ : Unit=>⟨t,a⟩) w)‖ ≤ o * ∏ i,D i:=by
    let G:= frozen C v; let Y' := frozen C w; let V (_ : Unit):C.book.Token:= ⟨t,a⟩; let W:ReadLabel C V:= fun _=>P; rw [← beside_commutes] at hf hx; rw [← beside_commutes,← beside_commutes]
    let S:Cylinder C:=fun N p=> register C k x (germ G) N p - C.O N p (P (N,p)) 0; have hv(j): Tendsto (combine G Y' j) 𝓕 (𝓝 ((beside v w j).2)):=by cases j <;> exact tendsto_const_nhds
    have hu(j):Tendsto (combine W Y' j) 𝓕 (𝓝 ((beside V w j).2)):=by cases j; exact hz; exact tendsto_const_nhds
    have hl: Gap C.S k Z0 (2*C.S.a b):=fun i j h=> (h (Subsingleton.elim ..)).elim
    have hQ: TileDoc U k 𝓕 (viewing U ((T') ∘ beside x y) (beside v w) - viewing U ((T') ∘ beside Z0 y) (beside V w))
        (register C k (beside x y) (germ (combine G Y')) - register C k (beside Z0 y) (germ (combine W Y'))):= TileDoc.diff U hf hx hv hu
    apply le_trans (TileDoc.global U hQ (B:=fun _ : Unit=>o) h hk hr hl hp hd he (z:=fun _=> S) (w:=germ Y') (fun _=> hB) (fun j=> (hD j).filter_mono hr) ?_) (by simp)
    filter_upwards with i; let R:Cylinder C:= fun N p=> C.O N p (P (N,p)) 0; simp only [Pi.sub_apply]
    rw [works,works, just_one S, show germ W =(fun _=>R) from rfl, just_one R]; unfold S; rw [sub_mul]
end YM.OPE
