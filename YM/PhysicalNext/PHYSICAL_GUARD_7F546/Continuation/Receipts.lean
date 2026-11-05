import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Sights
import YM.UVNext.PRICED_KERNELS.Seats


/-!
# Receipts of the weighted comparison, arranged for the curl step
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Gaussian
open UVNext.PricedKernels Extra.Iteration Extra.Iteration.Scales YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local
open MeasureTheory SectorTools.PhysicalGaussianSwitch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f : Side} {S : StepData c f} {A : Stores S}
  {I : Type} {F : Forest S.ratio} {x : ℝ}

def forecastFare (G : Gauge) (D : ℕ) (x : ℝ) := ((1+8*meter x)+4*Fintype.card G.ColorIndex)^D
lemma forecastFare_nn (G : Gauge) (D : ℕ) (x : ℝ) : 0 ≤ forecastFare G D x := by
  have := meter_pos x; unfold forecastFare; positivity


structure Rates (G : Gauge) (P : Patch) (D : ℕ) (x β U : ℝ) : Prop where
  big : 1 ≤ x
  high : 0 < β
  alive : 0 < fiery G x P.L
  forecastPrice : fiery G x P.L/coupling β ≤ 4*meter x
  offPrice : 1+2/coupling β+4*meter x ≤ x
  closePrice : D*(1+8*meter x)^D*x^(-(1/8):ℝ) ≤ x^(-(1/16):ℝ)
  flagPrice : x^(-(2:ℝ))*x * forecastFare G D x +
    forecastFare G D x * (momentFare (ceiling G P x) D U/x) ≤ x^(-(1/16):ℝ)
  tailPrice : x^(-(↑D+2):ℝ)*x^(D:ℕ) ≤ x^(-(1/16):ℝ)
  sigmaPrice : forecastFare G D x * errorFare (ceiling G P x) D U x ≤ x^(-(1/16):ℝ)



section receipt
variable {E : Type} [NormedAddCommGroup E]
variable [Fintype I] (P : I → Occasion G f) (r : I → G.El)

/-- Pull any polynomial class test back via the first-order forecast;
't/g' converted to meters. -/
lemma forecast_price {W : Finset (Bond f)} {o : Site c} {X : Support f} {l : ℕ}
    (h : Looks P X l x) (hh : Clears A x o (radiusB x)) (he : Covers X W) (hp : Reachable S o x W)
    {b : Vec I} (hb : ‖b‖ ≤ 8*meter x) {Q : Vec I → E} {D : ℕ} {c' : ℝ} (hQ : TestPrice Q D c') :
    TestPrice (fun z : Vec (SlotsW A F x W G) => Q (b+wind P r z)) D (c'*forecastFare G D x) := by
  have hi := meter_pos x
  have hv : Measurable (fun z : Vec (SlotsW A F x W G) => b+wind P r z) :=
    measurable_const.add
      ((funext (read_wind (W:=W) (F:=F) (x:=x) (A:=A) P r)) ▸ (view_cont _).measurable)
  refine ⟨mul_nonneg hQ.nonneg (forecastFare_nn ..), hQ.measurable.comp_measurable hv, ?_⟩
  intro z
  rw [mul_assoc]; apply (hQ.size _).trans (mul_le_mul_of_nonneg_left ?_ hQ.nonneg)
  have hz := (norm_add_le b (wind P r z)).trans (add_le_add hb (wind_cost P r hh h he hp z))
  unfold weight forecastFare
  rw [← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith [norm_nonneg z]

/-- Price the actual full integrand, not bounded by a degree-independent
constant in these units. -/
lemma sample_price {W : Patch} {β U : ℝ} {D : ℕ} (h : Rates G W D x β U)
    (R : Vec I → E) {a : ℝ} (hR : TestPrice R D a) (u : Vec I) (hu : ‖u‖ ≤ fiery G x W.L/coupling β) :
    let H : Config G f → E := fun V => R (sampled P r (coupling β) V-u)
    StronglyMeasurable H ∧ ∀ V, ‖H V‖ ≤ a*x^D := by
  intro H
  refine ⟨hR.measurable.comp_measurable ((sampled_cont P r _).sub continuous_const).measurable,fun V => ?_⟩
  have hg := coupling_pos h.high
  apply (hR.size _).trans (mul_le_mul_of_nonneg_left ?_ hR.nonneg)
  apply pow_le_pow_left₀ (by positivity)
  have ht := h.offPrice
  linarith only [ht,(norm_sub_le (sampled P r (coupling β) V) u).trans
    (add_le_add (sampled_bound P r hg V) (hu.trans h.forecastPrice))]
end receipt
end YM.PhysicalNext.PhysicalGuard7f546.Curved
