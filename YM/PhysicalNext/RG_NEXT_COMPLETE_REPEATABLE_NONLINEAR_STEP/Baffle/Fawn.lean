import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Vault
import YM.Progress.DIRECTED_RECIPE.Deploy

/-!
# Kinematics for using Γ only on its tube

Off χ boundaries of any edge. In particular ensure forced E6 cut=1 whenever
 a V9 Γ linear test needs it. Consume physical health gate after transferring
 to V at center of chart on same stencil. No continuity on E itself asked
 (derivatives in output through paying only masked old values).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c} {E : Support f} (a : Museum F X.x (bareStores S) E Y I)
variable {W : Config G f} {ζ d A β b t : ℝ} [Fintype I] (h : Canary G d A) (hp : 0<β) (v : Prices G I)
section drives
variable (q : Chi)
include h hp
omit h in
lemma credits (V:Config G c) (b d : ℝ) (i : I) : volume9 X a q 1 b i V + gStep β • tape (reading9 X V a v q b d β) i = fawn X V a v d β i := by
  have he:=record9 X V a hp v q b d i; unfold Museum.deposited at he; rw [a.seat.injective.extend_apply] at he; exact he

omit hp in
lemma sunny (i:I) : fawn X X.V a v d β i=anchor X a v β i := by unfold fawn; rw [Silica.action,mul_inv_cancel,G.mat_one,nothing_f h,id_eq]
lemma sun (i : I) (b : ℝ) :
    fawn X V a v d β i-anchor X a v β i= volume9 X a q 1 b i V-volume9 X a q 1 b i X.V +
      gStep β • (tape (reading9 X V a v q b d β) i - tape (reading9 X X.V a v q b d β) i) := by
  rw [← sunny X a h v i,← credits X a hp,← credits X a hp,smul_sub]; abel

variable {J : Type} [TopologicalSpace J] {Z : J→ Config G c} {x:J}

omit hp in
lemma homing (hZ : Tendsto Z (𝓝 x) (𝓝 X.V)) (he : 0 < t) :
    ∀ᶠ z in 𝓝 x, ∀ (u:Prices G I) i, ‖fawn X (Z z) a u d β i-anchor X a u β i‖ < t := by
  have hf : ∀ᶠ M in 𝓝 (1:G.Mat), ∀ u:G.Color, ‖Eider.plume G X.χ d M u‖ < t := by
    let U:= closedBall (0:G.Color) (2*d); let H:= {v:G.Mat×G.Color| ‖Eider.plume G X.χ d v.1 v.2‖<t}
    have ho (i : G.Color) : ContinuousAt (fun v:G.Mat × G.Color=>Eider.plume G X.χ d v.1 v.2) (1,i) := (Eider.sheen h X.χ i 1 (by simp [h.side.le])).continuousAt
    have h₁ (i : G.Color) : H∈𝓝 (1,i):= (ho i).norm.eventually (gt_mem_nhds (show ‖Eider.plume G X.χ d 1 i‖<t by rw [Eider.nothing h,norm_zero]; exact he))
    obtain ⟨u,s,hU,-,hV,hX,hF⟩:= generalized_tube_lemma (isCompact_singleton (x:=(1:G.Mat))) (show IsCompact U from isCompact_closedBall _ _) (isOpen_interior (s:=H)) (show {(1:G.Mat)}×ˢ U⊆ _ from by
      rintro ⟨b,c⟩ ⟨hb,hc⟩; have hh:b=1:=Set.mem_singleton_iff.mp hb; subst b; exact mem_interior_iff_mem_nhds.mpr (h₁ c))
    filter_upwards [hU.mem_nhds (hV (Set.mem_singleton 1))] with M hh z
    by_cases hv : z∈U
    · exact (show (M,z)∈H from interior_subset (hF (show (M,z)∈u×ˢ s from ⟨hh,hX hv⟩)))
    have hw : 2*d < ‖z‖ := lt_of_not_ge fun hm=>hv (mem_closedBall_zero_iff.mpr hm)
    rw [Eider.cooler h X.χ hw.le,norm_zero]; exact he
  have hg i:Tendsto (fun y=> G.mat (Silica.action X (Z y) (a.address i))) (𝓝 x) (𝓝 1):= by
    let g y:= G.mat (Silica.action X y (a.address i)); have he:g X.V=1:= by simp [g,Silica.action]
    rw [← he]; exact ((show Continuous g from (show Continuous G.mat by fun_prop).comp (continuous_const.mul ((continuous_apply _).comp Art.loyal).inv)).continuousAt).tendsto.comp hZ
  have hb (i:I) := (hg i).eventually hf
  filter_upwards [eventually_all.mpr hb] with z hz u i
  unfold fawn fleece; rw [add_sub_cancel_left]; exact hz i _

lemma portal_gap (b : ℝ) (hZ : Tendsto Z (𝓝 x) (𝓝 X.V)) (hx : ∀ i, Tendsto (volume9 X a q 1 b i ∘ Z) (𝓝 x) (𝓝 (volume9 X a q 1 b i X.V))) (hh : 0<t) :
    ∀ᶠ z in 𝓝 x, ∀ (u : Prices G I) i, gStep β * ‖tape (reading9 X X.V a u q b d β) i -tape (reading9 X (Z z) a u q b d β) i‖ ≤ t := by
  have he i : ∀ᶠ y in 𝓝 x,‖volume9 X a q 1 b i X.V-volume9 X a q 1 b i (Z y)‖≤ t/2 := by
    refine ((tendsto_const_nhds.sub (hx i)).norm.eventually (p:=(·≤t/2)) (ge_mem_nhds ?_)); rw [sub_self,norm_zero]; positivity
  filter_upwards [homing (β:=β) X a h hZ (half_pos hh),eventually_all.mpr he] with z hz hh u i
  have hr := hh i; have hp' := hz u i; let g:=gStep β; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hp)
  let U := tape (reading9 X X.V a u q b d β) i; let V:=tape (reading9 X (Z z) a u q b d β) i
  let W:=fawn X (Z z) a u d β i-anchor X a u β i; let Y:= volume9 X a q 1 b i X.V-volume9 X a q 1 b i (Z z)
  have hw : g • (V-U)=W+Y := by unfold W; rw [sun X a h hp u q i b]; unfold g V U Y; abel
  change g*‖U-V‖ ≤ t; rw [norm_sub_rev,← Real.norm_of_nonneg hg.le,← norm_smul]
  rw [hw]; apply (norm_add_le W Y).trans; unfold W Y; linarith
end drives
end YM.PhysicalNext.Repeat.Baffle
