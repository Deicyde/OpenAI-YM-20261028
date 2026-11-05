import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Issue.Cut.Bounds
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Space

/-!
# Capped path and entries under the charged blend

Suffix estimates for KP cq-type single W probes. Before all x,
issue shared funding for re-cutting **at the same output data**
(H and lower etc actually current, using `Towers` and explicit all-side
fixed numbers on high kernel supporting the cover). Nontrivial; there
is no assertion from Workshop/H alone that these *additional* spectral
inputs have been delivered in any Rank history. All cut operands use lifted
(per period `E` casting with `S.patch/P`, intended exact V table)
coefficients, estimates at x powers proved PRIOR to the caller's mask
or orientation choice. Not a `K.root` approximation or supplying
covariance atlas comparison away from this S patch. Does not purchase
history/Ranks. `unbox` prices even cuts with more restrictions if stage
imposes (see also E signed requirements not asserted to follow from
the regular local comparison). HUGE sensitivity to beta; use same-leg
comparison relation, don't assert that by rewriting clocks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
open AnalyticBridge.LocalGaussianLaws Venue   
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Laurent Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure Presented Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent Remote Lift Extra.Iteration.Scales MeasureTheory Local Work.F08 Next.Rank
open Primitives.GCC.LocalPolynomial (Script)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

/-- one sufficient ratio payment. Eg fixed-L,O(log x) comparison:
still need a supplier EVEN then. Follows just from |β'-β| power bill. -/
lemma earns : ∀ᶠ x : ℝ in atTop, ∀ β β' : ℝ, x/2≤β → x/2≤β' →
    |β'-β| ≤ x^(3/4:ℝ) → relativePay β β' x := by
  filter_upwards [eventually_gt_atTop (0:ℝ),(tendsto_rpow_atTop (show 0 < (1/8:ℝ) by norm_num)).eventually_ge_atTop 2]
    with x hx he β β' h1 h2 h3
  let b:=Real.sqrt β; let b':=Real.sqrt β'
  have hβ : 0 < β := by linarith
  have hβ' : 0 < β' := by linarith
  have hb : 0 < b := Real.sqrt_pos.2 hβ; have hb' : 0 < b' := Real.sqrt_pos.2 hβ'
  have hr : β=b*b := by unfold b; rw [Real.mul_self_sqrt hβ.le]
  have hr' : β'=b'*b' := by unfold b'; rw [Real.mul_self_sqrt hβ'.le]
  unfold relativePay coupling; rw [inv_inv]
  change |b'*b⁻¹-1| ≤ _
  let u:=coupler x; have hu : 0≤u := Real.rpow_nonneg hx.le _
  have hz : x^(3/4:ℝ) ≤ x/2*u := by
    have hf := mul_le_mul_of_nonneg_right he (show 0 ≤ x^(3/4:ℝ) from Real.rpow_nonneg hx.le _)
    have hh : x ^ (1/8:ℝ)*x^(3/4:ℝ)=x*u := by
      unfold u coupler; nth_rw 3 [← Real.rpow_one x]; rw [← Real.rpow_add hx,← Real.rpow_add hx]; norm_num
    linarith only [hf,hh]
  have h0 := le_trans (le_trans h3 hz) (mul_le_mul_of_nonneg_right h1 hu)
  have h : |β'-β|=|b'-b| * (b'+b) := by rw [hr',hr,show b'*b'-b*b=(b'-b)*(b'+b) from by ring,abs_mul,abs_of_nonneg (by positivity : 0≤b'+b)]
  have hh : |b'-b| * b≤b*(b*u) := (mul_le_mul_of_nonneg_left (show b≤b'+b by linarith) (abs_nonneg _)).trans (by rw [h,hr,mul_assoc] at h0; exact h0)
  rw [← div_eq_mul_inv,show b'/b-1=(b'-b)/b from by field_simp, abs_div,abs_of_nonneg hb.le,div_le_iff₀ hb]
  rw [mul_comm]; exact le_of_mul_le_mul_left (by linarith only [hh]) hb



section commerce
variable {tier : ℕ} {G : Gauge} {c f : Side} {S : StepData c f} {H B : Bed} {T : Tube G S} {x E R β β' ε : ℝ}
variable {V : Config G c} {W : Site c→ G.El} {v : Dir G c} {o : Site c} {F : Forest S.ratio} {A : Stores S}
variable (Pt : Teller G) (hp : Pt.Funds S T) (hR : 1≤R) (HO : Board tier x R A T H o V F W v) {K D : ℕ}
    (hc : Account tier K D E x A T H o V F W v) (hK : D+1 ≤ K) (he : Clears A x o (vista tier x))
    (k : S.Choices) (q : Chi) (d : ℝ) (u' : Assembly.Geometry) (Y : LinkArray G (Frozen A x F))
variable {I : Type} [Fintype I]
include hp hR HO hc hK he


end commerce


end YM.PhysicalNext.WeightedGaussianMarginal45C.Issue.Cut
