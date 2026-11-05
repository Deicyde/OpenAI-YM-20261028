import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Rainy
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
/-!
# Exponential comparison coupon. No assumptions on normalized ∆ dictionary variation as V, at point only factorial-size nonhomogeneous. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented   Bid 
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums   
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {j : ℕ}
open Set
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type} {n : ℕ} {v u r s : ℝ}
lemma walks (g h' : F→ E→ℝ) (f: F→ℝ) (x:E) (p : Finset F) (he : 0 ≤ r) (hy : r ≤1)
    (hg : ∀ i∈p, Brush n (f i) 1 (g i) x) (hh : ∀ i∈p, Brush n (r*f i) 1 (h' i-g i) x):
      let k := fun (i:F) => 3*3^n*f i; let v:=∏ i∈p,k i
      Brush n v 1 (fun y=>∏ i∈p,h' i y) x ∧ Brush n (r * v) 1 (fun y=> (∏ i∈p,h' i y)-(∏ i∈p,g i y)) x := by
  induction p using Finset.induction_on with
  | empty=>
    intro k v; simp_rw [Finset.prod_empty]; have ht : v=1:=Finset.prod_empty; rw [ht]; simp only [sub_self,mul_one]; exact ⟨by simpa only [norm_one] using Brush.certified (k:=n) (x:=x) zero_le_one (1:ℝ), Brush.zi (EventuallyEq.rfl) he zero_le_one⟩
  | insert i s hi ih=>
    obtain ⟨hH,hp⟩:=ih (fun i ht=> hg _ (mem_insert_of_mem ht)) (fun i ht=> hh _ (mem_insert_of_mem ht))
    intro k v; let q:=∏ i∈s,k i; have ht:v= k i*q:= Finset.prod_insert hi
    have hQ:0 ≤ q := hH.nonneg
    let F y:=∏ i∈s,g i y; let G y:=∏ i∈s,h' i y
    have h := hg i (mem_insert_self ..)
    have he' := hh i (mem_insert_self ..)
    have hσ : Brush n (2*f i) 1 (h' i) x:= by refine (((h.gathering he').climb ?_ le_rfl).shimmy (Eventually.of_forall fun _=> (add_sub_cancel ..).symm)); rw [two_mul]; exact add_le_add le_rfl (mul_le_of_le_one_left h.nonneg hy)
    have hG:0≤f i:= h.nonneg
    have hv:F+(G-F)=G:=by funext; exact add_sub_cancel ..
    have hz := he'.paints hH; have hu := h.paints hp
    simp_rw [prod_insert hi]; rw [ht]; constructor
    · refine (hσ.paints hH|>.trim).climb ?_ le_rfl; change _*q* _≤k i*q; unfold k
      norm_num; nlinarith only [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤3) n) (mul_nonneg hG hQ)]
    refine (((hz.gathering hu).trim).climb ?_ le_rfl).shimmy (Eventually.of_forall fun i'=>?_)
    · change ((r*f i)*q+f i*(r*q))*(1+(1+1))^n≤_; rw [show (1:ℝ)+(1+1)=3 by ring]; unfold k; nlinarith only [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤3) n) (mul_nonneg (mul_nonneg he hG) hQ)]
    · change h' i i'*G i'-g i i'*F i' = (h' i i' - g i i')*G i' + g i i' *(G i'-F i'); ring

-- usable for upper deriv ≥ λ under sal. No p cardinal attenuation, just actual finite lattice 
lemma insured (f h : F→ℝ) (t : ℝ) (j : ℕ) (hs : SumBudget f s) (hp : SumBudget h (u*t)) (ht:0<t) :
    let a i:= f i+h i/t
    SumBudget (fun p : Finset F=> ∏ i∈p,3*(3:ℝ)^j*a i) (Real.exp (3*3^j*(s+u))) := by
  intro a; apply AbsoluteSums.Product.set_products; apply budget_scale (by positivity); apply budget_plus hs
  have he := budget_scale (show 0 ≤ t⁻¹ from (inv_pos.mpr ht).le) hp
  simp_rw [show t⁻¹*(u*t)=u by field_simp] at he; convert he using 1; ext; ring
end YM.PhysicalNext.Repeat.Alabaster
