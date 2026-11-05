import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Mural
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Shawl
/-! # NormJ of warp ratio along M-angles. Vanishes with δ, uniform warp polynomial and scale moment under ORIGINAL true S.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider Reserves Brush Metric Foramen Gate Tablet
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {W : ℝ}
variable {Q : ConnectedActivityE6.Target G P} {o : Target.Order G W} {R I : RG.Rep G f}
    {p μ C v D' d r D K' : ℝ} {i j n m : ℕ} {χ : Chi} {H : Cash W p μ L Q o C T R} {η εK θ β a h g l b Y A q e r' u : ℝ}
local notation "F₀" => (facescale (univ:Finset (Bond f)))
local notation "w" => low R I
section atlas
variable {t : ℝ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E}
-- Exponent anchored. even ≤1 via rescaling derivative toll not coefficient.
lemma wrapsAid {f:E→ℝ} (u : ℝ) (hv:1≤u) (ht : Brush j (e*u) 1 f x) (ha:f x=0) (he : 0 ≤ e) : Brush j e u f x := by
  refine ⟨ht.smooth,zero_le_one.trans hv,?_⟩; intro i hi; by_cases h:i=0
  · rw [h,normJ,norm_iteratedFDeriv_zero,ha,norm_zero,pow_zero,mul_one]; exact he
  have hk:= ht.order _ hi; rw [one_pow,mul_one] at hk; exact hk.trans (mul_le_mul_of_nonneg_left (le_self_pow₀ hv h) he)
def ear (j : ℕ) (S W : ℝ) := W*(1+(S+S))^j*2^j
lemma crystals (j : ℕ) (C' : ℝ) (he : 0 ≤ C') : ∃ M : ℝ, 0 ≤ M ∧ ∀ (s t A : ℝ),0 ≤ s → s ≤1 → |1-t| ≤ s → 1≤ A → ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (y:E) (f:E→ℝ), Brush j (C'*A^2) 1 f y → Brush j (s*M*A^(2*j)) 1 (fun x=> Real.exp ((1-t)*(f x-f y))-1) y:= by
  obtain ⟨W,hW,H⟩:=Brush.expands j; refine ⟨ear j C' W,by unfold ear; positivity,?_⟩; intro s t A hs hv hk hp E _ _ y f hr
  let p:= (1+(C'+C'))*A^2; have hh: 1 ≤ p:= one_le_mul_of_one_le_of_one_le (le_add_of_nonneg_right (add_nonneg he he)) (one_le_pow₀ hp)
  have hc:= (hr.separating ((Brush.certified zero_le_one _).climb hr.bound le_rfl)).smul (1-t)
  let g(x:E):=(1-t)*(f x-f y)
  have hg:Brush j (s*p) 1 g y:=hc.climb (le_trans (mul_le_mul_of_nonneg_right hk (by positivity)) (mul_le_mul_of_nonneg_left (by unfold p; nlinarith only [le_self_pow₀ (n:=2) hp (by decide),hp]) hs)) le_rfl
  refine ((H _ _ s p g (wrapsAid p hh hg (by unfold g; ring) hs) hv).trim).climb ?_ le_rfl
  apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith : 0 ≤ 1+p) (show 1+p ≤2*p by linarith) j) (mul_nonneg hW hs)) _; unfold p ear; rw [mul_pow,mul_pow, pow_mul]; exact le_of_eq (by ring)

end atlas
end YM.PhysicalNext.Repeat.Alabaster
