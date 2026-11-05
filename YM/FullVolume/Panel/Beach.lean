import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Marchers

/-!
# Shape budgets for angular sup marks and genuine `Regular`

 Absolute merged marks separate. Pays at anchored P compatible with
 old History threshold and new generation etc, but no Taylor vanishing claim!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider  Hues Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {j n l k : ℕ} {R : Rep G f} {X : Coat T F} {I : Finset (Tubular f G)} {η r q a Y W d C' A b s μ C v B: ℝ} {Ñ : ChartRatio G}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {χ : Chi}
variable {H : Cash W s μ L Q o C T R} {Ξ : Utopia H j v d r C' χ}
open Next.Foundations

lemma trust {V:Config G c} {f g :Config G c→ℝ} (hv:0<v) (hp:∀ (U:Directions G c→ Config G c),Mode U 0 j v→ U 0=V→ f ∘ U=ᶠ[𝓝 0] g ∘ U):
    f ∘ increment V=ᶠ[𝓝 0] g ∘ increment V := by
  obtain ⟨u,hu,h⟩:= expCost G j 1
  let a:=1+j.factorial*u; have ha : 0<a := by unfold a; positivity
  let d:= v/(2*a); have hd : 0<d:= by unfold d; positivity
  let L := d • ContinuousLinearMap.id ℝ (Directions G c)
  have hL : ‖L‖ ≤ 1*d := by unfold L; rw [norm_smul,one_mul,Real.norm_of_nonneg hd.le]; exact mul_le_of_le_one_right hd.le ContinuousLinearMap.norm_id_le
  have hh := fromLogL L (x:=0) (linearB L (u:=1) (d:=d) (by simp) hL hd.le) 1 zero_lt_one h (by intro i; simp only [map_zero, Pi.zero_apply]; simp) V
  have he : (1+(j.factorial:ℝ)*u)*((1+1)*d)=v := by change a*_ =_; unfold d; field_simp; ring
  rw [he] at hh
  let M:= d⁻¹ • ContinuousLinearMap.id ℝ (Directions G c)
  have hP:=(hp (fun a=> increment V (L a)) hh (by rw [map_zero]; exact Work.G07.at_zero_increment V)).comp_tendsto (show Tendsto M (𝓝 0) (𝓝 0) from by simpa only [map_zero] using M.continuous.tendsto 0); filter_upwards [hP] with x hx; change _ = _; simpa only [Function.comp_apply,L,M,ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,smul_smul,mul_inv_cancel₀ hd.ne',one_smul] using hx
end YM.ConnectedActivityE6.Blaze.March
