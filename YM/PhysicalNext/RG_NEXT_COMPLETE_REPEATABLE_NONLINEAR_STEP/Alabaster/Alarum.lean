import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Satin
/-! # K warp rays: a compulsory estimate. Second Step selectors may alter β
 *without* changing orientations or leaving mask. Need only lower bill price,
 not upper bound on actual tag energies. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {P : Teller G} {W : ℝ} {K C : ℝ}

lemma ponds (x y c : ℝ) (hx : x ≤ c) (hy : y ≤ c) :
    |Real.exp x-Real.exp y|≤ Real.exp c * |x-y| := by
  have h := (convex_Iic c).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=Real.exp) (fun z _=> Real.differentiableAt_exp)
    (fun i (hi:i∈Set.Iic c)=> (by rw [← norm_deriv_eq_norm_fderiv,Real.deriv_exp,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hi)) hy hx
  exact h

lemma notchCost (b : ℝ) (hb : 0 < b) (d A n: ℝ) (hd : 0 ≤ d) (hn : 0 ≤ n) : ∃ K:ℝ, 0 ≤ K ∧
    ∀ l m u x y B:ℝ, -d ≤ u → |B-b|≤ l → |y-x|≤ l*n → x≤ A → 0 ≤ l → l ≤ 1 → l≤ b/2 → 0 ≤ m →
       |m * Real.exp (-B*u+y)-m * Real.exp (-b*u+x)|≤ l*m*K := by
  let D:=A+n+(b+1)*d; let c:= b/2; have hC:0<c:=by unfold c; positivity
  let W:=c⁻¹+n; let V:=Real.exp D
  have hw:0 ≤ W:=by unfold W; positivity
  have hv : 0 ≤ V := (Real.exp_pos _).le
  have ht := mul_nonneg (add_nonneg hd hn) hv
  refine ⟨(d+n)*V+W*V, add_nonneg ht (mul_nonneg hw hv),?_⟩; intro l m u x y B hu hh hg hx hL hL' h₀ hy
  have hh' : c≤B:= by unfold c; linarith only [(abs_le.mp hh).1,h₀]
  have hx': y ≤ A+n := by linarith only [(abs_le.mp hg).2,hx,mul_le_of_le_one_left hn hL']
  have hs:B≤ b+1:= by linarith only [(abs_le.mp hh).2,hL']
  rw [← mul_sub,abs_mul,abs_of_nonneg hy, mul_comm l,mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ hy
  have hp: |-B*u+y-(-b*u+x)|≤ l*(|u|+n):= by
    rw [show -B*u+y-(-b*u+x)= - (B-b)*u+(y-x) by ring]; apply (abs_add_le ..).trans; rw [abs_mul,abs_neg,mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right hh (abs_nonneg _)) hg
  rcases le_or_gt u 0 with h|h
  · have hx : -b*u+x≤D := by unfold D; nlinarith only [mul_le_mul_of_nonneg_left hu hb.le,hx,hd,hn]
    have hB : -B*u+y≤D:= by unfold D; nlinarith only [hx',mul_le_mul_of_nonneg_left hu (hC.le.trans hh'),mul_le_mul_of_nonneg_right hs hd]
    apply (ponds _ _ D hB hx).trans; rw [abs_of_nonpos h] at hp; rw [mul_add]
    refine (mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left (add_le_add_left (neg_le.mp hu) _) hL)) hv).trans ?_
    exact (le_of_eq (by change V*_=l*((d+n)*V); ring)).trans (le_add_of_nonneg_right (by positivity))
  have hs' : b ≥ c:= by unfold c; linarith only [hb]
  have hA' : A+n ≤ D:=le_add_of_nonneg_right (mul_nonneg (by linarith only [hb]) hd)
  have hh₁ := ponds _ _ (D-c*u) (show -B*u+y≤_ from (by nlinarith only [hx'.trans hA',mul_le_mul_of_nonneg_right hh' h.le]))
    (show -b*u+x≤_ from (by nlinarith only [mul_le_mul_of_nonneg_right hs' h.le,hx,hA',hn]))
  apply (hh₁.trans (mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _))).trans
  rw [Real.exp_sub,abs_of_pos h]; have hH := Real.add_one_le_exp (c*u); have hT := Real.exp_pos (c*u); have hg : 1 ≤ Real.exp (c*u):= Real.one_le_exp (mul_nonneg hC.le h.le)
  let z:= Real.exp (c*u); have he:u≤ z*c⁻¹:= by rw [← div_eq_mul_inv,le_div_iff₀ hC]; unfold z; linarith
  calc
    _ = l*(V*((u+n)/z)) := by unfold V z; ring
    _ ≤ l*(V*W):= mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ((div_le_iff₀ hT).2 (by unfold W; nlinarith only [he,show n≤ z*n from le_mul_of_one_le_left hn hg])) hv) hL
    _ ≤ _ := by rw [mul_comm V W]; exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ht) hL
end YM.PhysicalNext.Repeat.Alabaster
