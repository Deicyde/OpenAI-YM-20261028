import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts
/-!
# Numerical voucher all on single month step. Redemption includes strict breathing-affine-station radius stability.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sienna
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {f w : ℝ→ℝ} {p C η σ l : ℝ} {n : ℕ} {Q : KernelChoices} {c g : Side}
local notation "μ" => Delay.fineMonitor G L
local notation "U" => eaves G L
local notation "M" => furl G L
local notation "F" => (fun t=> Pressure.fiery G t L)
local notation "Z" => (fun t=> betaF G t L)
structure Pigment (n:ℕ) (V : ChartPrices) (O : ChartRatio G) (R b v u x s m : ℝ) : Prop where
  top : 0 < u
  booth : 0<b
  lease : b<u
  positive : 0≤R
  small : u≤ 1
  horizon : u≤ V.horizon
  shade : Uniform.shade G*u < min V.horizon 1
  initial : (1+Before.Service.trailCost V (n+3))*u +u*R < V.initial
  one : (1+Before.Service.trailCost V (n+3))*u+u*R<1
  count : Uniform.shade G*(Before.Service.trailCost V (n+3)*u+u*R) ≤ O.radius/2
  sermon : v*((1+ Before.Service.trailCost V (n+3))*m + b*(R+R)) ≤ s/2
variable (d r X : ℝ) (V : ChartPrices) (O : ChartRatio G) (ho : LocalRatio O)
local notation "T" => Before.Service.trailCost V (n+3)
def pence (x : ℝ) := (16*x)⁻¹
include ho
lemma pencils (ht : 0<X) (hh : 0 < V.horizon) (hg : 0<V.initial) :
    ∀ᶠ t in atTop, ∀ β, Z t/2 ≤ β → Pigment n V O (wick G L (pence X) t) (gStep β) X (U t) t (F t) (M t) := by
  let D :=pence X; have hd: 0<D:=by unfold D pence; positivity
  let S:=1+T; let s:= min V.horizon 1; have hz:0<s:=lt_min hh zero_lt_one
  -- first conditions
  have h' := billsV G L D hd S O.radius V.horizon (min V.initial 1) hh ho.patch (lt_min hg zero_lt_one)
  have hK:= below' G L ((edge G L).mul_left (Uniform.shade G)) vow_ok hz
  filter_upwards [Delay.shift_pos G L, h',hK, puff (L:=L) G (X*S) (1/4) (by norm_num)] with t ht' hx hy hu β hb
  obtain ⟨ha,hb',hP,hx,hQ,hR,hG⟩:=hx; obtain ⟨hp,hB⟩:=hG β hb; let M':= Delay.fineMonitor G L t
  refine ⟨ha,hp,hB,hb'.le,hP,hQ.le,hy,hx.trans_le (min_le_left ..),hx.trans_le (min_le_right ..),?_,?_⟩
  · apply le_trans _ hR; apply mul_le_mul_of_nonneg_left _ (Uniform.shade_pos G).le; apply add_le_add _ le_rfl; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) ha.le
  have hg : X*(gStep β* (wick G L D t+wick G L D t))≤ (F t)/4:= by
    apply le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (lamp G L ht' β hb|>.2) (add_pos hb' hb' |>.le)) ht.le); apply le_of_eq; change X*((2*gStep (Z t))*(D*M'+D*M'))=(gStep (Z t)*M')/4; unfold D pence; field_simp; ring
  linarith only [hg,hu]
end YM.PhysicalNext.Repeat.Sienna
