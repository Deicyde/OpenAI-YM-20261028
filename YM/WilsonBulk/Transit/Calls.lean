import YM.WilsonBulk.Web.Patterns

/-!
# Transfer of many arguments through sparse elementary stencils

Costs with TWO different homogeneous widths passed at consecutive stage(s).
Notation `tollRank`: rank n (test point leg counts too); can shrink factor
n+1 on columns BEFORE block. Need for both `print` proxy mean & reblocking
and contraction of normalized vacuum packets with identical/different
predictor gauge. Non-tree path estimates not asserted. `WithRoute` may use
orientation-specific line maps on a subset of the legs, satisfying the same
invoice. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical Topology BigOperators ENNReal
open Pert.Bulk Function Equiv Filter Finset Lattice
variable {X Y T : Type} {δ σ θ p q p' q' M : ℝ} {D : Rule X} {E : Rule Y} {n m k : ℕ}

abbrev Duct (X Y : Type) := X→ Y→ℝ
abbrev Routes (n : ℕ) := Legs (Duct X Y) n -- fix implicit X Y?
def meters (T : Duct X Y) (K : Page X n) (i : Fin n) (x : Legs X n) (y : Legs Y n) := K x * T (x i) (y i) -- maybe unused

def lot (T : Legs (Duct X Y) n) (x : Legs X n) (y : Legs Y n) : ℝ :=
  ∏ i, T i (x i) (y i)
def metal (T : Legs (Duct X Y) n) (u : Page X n) (y : Legs Y n) (x : Legs X n) := lot T x y * u x
def tele (T : Legs (Duct X Y) n) (u : Page X n) : Page Y n := fun v=>
  ∑' x, metal T u v x
def travel (T : Duct X Y) := fun K : Page X n=> tele (fun _=>T) K
lemma teleport_escort (K : Legs (Duct X Y) m) (e : Fin n≃ Fin m) (u : Page X m) :
    tele (K ∘ e) (escort e.symm u)=escort e.symm (tele K u) := by
  ext1 v; unfold escort tele; rw [← (casesEquiv e (Equiv.refl _)).tsum_eq _]; apply tsum_congr; intro x
  unfold metal; congr 1; unfold lot; rw [← Equiv.prod_comp e]; simp only [casesEquiv_apply,Function.comp_apply,Equiv.refl_apply,Equiv.symm_apply_apply]
lemma travel_regular (K : Duct X Y) {u : Page X n} (h : Regular u) : Regular (travel K u) := by
  intro e
  have he:= teleport_escort (fun _:Fin n=> K) e.symm u; rw [Equiv.symm_symm,h e] at he; exact he.symm
lemma travel_pervades {α β : Type} (e : Cover→ Cover) {K : Duct (Market α) (Market β)}
    (h : ∀ x y b,K (roll (e b) α x) (roll b β y) =K x y) {u : Text α n} (he : ∀ b, arabesque (roll (e b) α) u) : Pervasive (travel K u) := by
  intro b v; unfold travel tele; rw [← (casesEquiv (Equiv.refl _) (roll (e b) α)).tsum_eq (fun x=> metal (fun _=> K) u (roll b β ∘ v) x)]
  apply tsum_congr; intro x; unfold metal lot
  rw [show casesEquiv (Equiv.refl _) _ x= roll (e b) α ∘ x from by rw [casesEquiv_apply]; rfl,he]; simp only [Function.comp_apply,h]

structure AuditLine (T d : Duct X Y) (n : ℕ) (p q : ℝ) : Prop where
 height : 0 ≤ p
 floor : 0 ≤ q
 fronts x y : 0 ≤ d x y
 row x : ∑'y,bill (T x y) (d x y) ≤ ENNReal.ofReal p
 col y : ∑'x,bill (T x y) (n*d x y) ≤ ENNReal.ofReal q

variable {d A B : Duct X Y}
namespace AuditLine
variable (h : AuditLine A d n p q)
include h
lemma narrow {e : Duct X Y} (hm : m≤n) (hh : p≤p') (hq : q≤q') (hw : ∀ x y, e x y ≤ d x y) (he : ∀ x y,0 ≤ e x y) : AuditLine A e m p' q' := by
  refine ⟨h.height.trans hh,h.floor.trans hq,he,fun x=>?_ ,fun y=>?_⟩
  · exact (ENNReal.tsum_le_tsum fun y=> bill_mono le_rfl (hw x y)).trans ((h.row x).trans (by gcongr))
  exact (ENNReal.tsum_le_tsum fun x=> bill_mono le_rfl (mul_le_mul (by exact_mod_cast hm) (hw x y) (he x y) (by positivity))).trans ((h.col y).trans (by gcongr))
lemma total_row (x : X) : Summable (A x) := summable_from_receipt (h.fronts x) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.row x))
lemma total_col (y : Y) : Summable fun x=> A x y := summable_from_receipt (fun _=>mul_nonneg (Nat.cast_nonneg n) (h.fronts ..)) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h.col y))
lemma entry (x : X) (y : Y) : |A x y| ≤ p := by
  rw [← ENNReal.ofReal_le_ofReal_iff h.height]
  exact (show ENNReal.ofReal |A x y|=bill (A x y) 0 from by simp [bill]).le.trans ((bill_mono le_rfl (h.fronts x y)).trans ((ENNReal.le_tsum y).trans (h.row _)))
lemma accumulate (h' : AuditLine B d n p' q') : AuditLine (A+B) d n (p+p') (q+q') := by
  have hx (x y b : ℝ) : bill (x+y) b ≤ bill x b+bill y b := by simpa [bill] using bill_sub x (-y) b
  refine ⟨add_nonneg h.height h'.height, add_nonneg h.floor h'.floor,h.fronts,fun x=>?_,fun y=>?_⟩
  · rw [ENNReal.ofReal_add h.height h'.height]
    refine LE.le.trans ?_ (add_le_add (h.row x) (h'.row x)); rw [← ENNReal.tsum_add]; exact ENNReal.tsum_le_tsum fun y=> hx ..
  rw [ENNReal.ofReal_add h.floor h'.floor]; refine LE.le.trans ?_ (add_le_add (h.col y) (h'.col y)); rw [← ENNReal.tsum_add]; exact ENNReal.tsum_le_tsum fun x=> hx ..
end AuditLine

def Geometry (D : Rule X) (E : Rule Y) (θ σ : ℝ) (d : Duct X Y) :=
  ∀ x z y w, σ*E.cost y w ≤ d x y + d z w + θ*D.cost x z
-- pointwise bounds for output root and all inputs for transferring rank n+1
lemma sticker (g : Geometry D E θ σ d) (hh : ∀ x y, 0≤ d x y)
    (x : X) (y : Y) (u : Legs X n) (v : Legs Y n) :
    σ*run E y v ≤ θ*run D x u + ((n+1:ℕ):ℝ)*d x y + ∑ i:Fin n,d (u i) (v i) := by
  unfold run; rw [mul_sum,mul_sum]
  apply LE.le.trans (sum_le_sum (fun i (_:i∈ (univ : Finset (Fin n)))=> g x (u i) y (v i)))
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; push_cast; have H:=hh x y; linarith
lemma metal_head (u : Legs X n) (v : Legs Y n) (x y) (T : Legs (Duct X Y) (n+1)) (P : Page X (n+1)) :
    metal T P (hitch y v) (hitch x u)= T 0 x y * (P (hitch x u)*lot (crop T) u v) := by
  simp only [metal,lot,Fin.prod_univ_succ,crop,hitch_zero,hitch_succ]; ring
variable {C : Legs (Duct X Y) (n+1)} {R S : Fin (n+1)→ℝ} {u : Page X n}
-- allow different row strengths per leg in telescoping argument
lemma till (g : Geometry D E θ σ d) (hc : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (P : Page X (n+1)) (hp : Within D θ p P) (y : Y) :
    ∑'x,∑' v : Legs Y n,bill (metal C P (hitch y v) x) (σ*run E y v) ≤
      ENNReal.ofReal (S 0 *(∏ i:Fin n,crop R i)*p) := by
  let T : Fin n→Duct X Y := crop C; let r : ℝ≥0∞:=∏ i: Fin n, ENNReal.ofReal (R i.succ)
  let a x := bill (C 0 x y) ((n+1:ℕ)*d x y); let b x u := bill (P (hitch x u)) (θ*run D x u)
  let s := S 0
  rw [ts_hitch]
  have h1 : ∑' x, a x ≤ ENNReal.ofReal s := (hc 0).col _
  have h2 x : ∑' u,b x u ≤ ENNReal.ofReal p := (rent_head P x).ge.trans (hp.2 0 x)
  calc
    _ ≤ ∑' x,∑' v:Legs X n,a x*b x v*r := ENNReal.tsum_le_tsum (fun x=> ENNReal.tsum_le_tsum (fun u=> by
          apply LE.le.trans (ENNReal.tsum_le_tsum (g:=fun v:Legs Y n=>a x*b x u * ∏ i,bill (T i (u i) (v i)) (d (u i) (v i))) (fun v=>?_)) ?_
          swap
          · rw [metal_head,← bill_products]; unfold a b; rw [← purchase, ← purchase]; unfold lot; rw [← mul_assoc]; exact bill_mono le_rfl ((sticker g (hc 0).fronts x y u v).trans_eq (by simp only [add_comm _ (θ * _)]))
          rw [ENNReal.tsum_mul_left,all_Δ (a:=fun i (v:Y)=>bill (T i (u i) v) (d (u i) v))]; apply mul_le_mul_right; exact Finset.prod_le_prod' (fun i _=> (hc i.succ).row (u i))))
    _ ≤ ENNReal.ofReal (S 0) * ENNReal.ofReal p * r := by
          simp_rw [ENNReal.tsum_mul_right,ENNReal.tsum_mul_left]; apply mul_le_mul_left; refine LE.le.trans (ENNReal.tsum_le_tsum (fun x=> mul_le_mul_right (h2 x) (a x))) ?_; rw [ENNReal.tsum_mul_right]; exact mul_le_mul_left h1 _
    _ = _ := by
          unfold r; have hs:= (hc 0).floor; have hv (i : Fin n) : 0≤crop R i:=(hc i.succ).height
          rw [mul_right_comm (S 0), ENNReal.ofReal_mul (mul_nonneg hs hp.1), ENNReal.ofReal_mul hs, ENNReal.ofReal_prod_of_nonneg]; exact fun i _=> hv i
end YM.WilsonBulk.Sheet
