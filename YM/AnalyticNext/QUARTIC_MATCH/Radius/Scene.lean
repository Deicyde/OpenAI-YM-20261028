import YM.AnalyticNext.QUARTIC_MATCH.Radius.Reach
import YM.AnalyticNext.QUARTIC_MATCH.Range

/-!
# ONE furnished room branch for every tag and displacement in those grants

Agreement with true representatives (as germs near 0). Includes every
coarse logarithmic field in this ball, not excluding any harmonic directions.
Not claiming equality of arbitrary extension of germ. For continuation use
this assembly with purchases before period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Radius
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes Work.F03 YM.Next.Free Tree Joint Local Local.Wages Polish Fetch Sheets
open Purchase Articles Showroom Model Warp
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Raised
open Orbit
variable {c f : Side} (S : StepData c f) (H : Forest S.ratio) (p : Clip) {G : Gauge} (R : PathData G)
variable {F : Site f→ChartVars H G→ℝ} {Q : Purchase} {η : ℝ}
    (hp : Q.Applies H p R F) (hr : 0<η) (hh : PriceGap H p R η)
variable {ρ : Dir G c → AxisChart G H} (h : Critical H p R ρ) (θ : S.Choices)
local notation "g" => GArray S H p R
local notation "x₀" => (0:ChartVars H G)
local notation "V" => Orbit.reserve Q G η
local notation "B" => Orbit.berth Q G η
include hp
lemma opens {y : ChartVars H G} (he : ‖y‖ < Q.width) :
    g θ y=0 ↔ HasFDerivAt (𝕜:=ℝ) (tested H θ p R y.1) 0 y.2 := by
  constructor
  · intro hz
    have hv : fderiv ℝ (tested H θ p R y.1) y.2=0 := by
      ext i
      rw [reveal S H i,map_sum,_root_.zero_apply]
      have ht (i : Key H G) := reads S H p R θ hp he (i:=i)
      simp_rw [map_smul,← ht,hz,Pi.zero_apply,smul_zero,Finset.sum_const_zero]
    rw [← hv]; exact ((Work.F05.hold_jet (works S H p R hp he θ)).differentiableAt (by simp)).hasFDerivAt
  intro hv; funext i; rw [reads S H p R θ hp he (i:=i), hv.fderiv]; rfl

include h


structure Reaches (Q : Purchase) (η : ℝ) (S : StepData c f) (H : Forest S.ratio) (p : Clip) (R : PathData G) (χ : Dir G c→ AxisChart G H) : Prop where
  origin : χ 0=0
  smooth x : ‖x‖< Orbit.berth Q G η → ContDiffAt ℝ ω χ x
  payments x : ‖x‖ < Orbit.berth Q G η → ‖χ x‖ < Orbit.reserve Q G η ∧
    ∀ t, GArray S H p R t (x,χ x)=0
  knows t x y z : ‖x‖ < Orbit.berth Q G η → ‖y‖ < Orbit.reserve Q G η →
    ‖z‖ < Orbit.reserve Q G η → GArray S H p R t (x,y)=0 → GArray S H p R t (x,z)=0 → y=z
include h
include hr hh

omit h
variable {χ : Dir G c→AxisChart G H} (hk : Reaches Q η S H p R χ)
include hk
omit hp hr hh in
lemma inside_r {x : Dir G c} (he : ‖x‖<B) : ‖(x,χ x)‖ < V := max_lt (he.trans_le (berth_paid ..)) ((hk.payments x he).1)
omit hr hh in
lemma station {x : Dir G c} (he : ‖x‖<B) : HasFDerivAt (𝕜:=ℝ) (tested H θ p R x) 0 (χ x) :=
    (opens S H p R hp θ ((inside_r S H p R hk he).trans (Orbit.room ..))).1 ((hk.payments x he).2 θ)
include h
omit hh in
lemma congruent : χ =ᶠ[𝓝 0] ρ := by
  have he : 0<B := paid Q G η hr; let t : S.Choices := Classical.arbitrary _
  have hv := h.2.1.continuousAt.tendsto; rw [h.1] at hv
  have ht : ∀ᶠ x : Dir G c in 𝓝 0, ‖ρ x‖< V := hv.eventually (nearInside (by rw [norm_zero]; exact booked Q G η hr))
  filter_upwards [ht,nearInside (show ‖(0:Dir G c)‖<B by rwa [norm_zero]), (h.2.2 t).2] with x hx hh hi
  apply hk.knows t x _ _ hh ((hk.payments x hh).1) hx ((hk.payments x hh).2 t)
  exact (opens S H p R hp t (y:=(x,ρ x)) ((max_lt (hh.trans_le (berth_paid ..)) hx).trans (Orbit.room ..))).mpr hi
end Raised
end YM.AnalyticNext.QuarticMatch.Radius
