import Mathlib.Data.Set.Finite.List
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Batch
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Brush
-- ContDiff Param utility

/-!
# Budgeted integration with probes

Combine with sup estimates using the *same* open stencil for all probes, ghost
 coordinates. Can't assume uniform integrability before P.Sear, but use
`ContinuousOn` for the interval-log votes. Also use on real section
change-of-variables density products *after* doing score checks and local domination.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function MeasureTheory
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F α : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace α]
open Brush
variable {x : E} {k j : ℕ} {U : E → α → F} {μ : Measure α}

abbrev JetF (U : E → α → F) (k : ℕ) (x : E) (a : α) := iteratedFDeriv ℝ k (fun x=> U x a) x

-- Includes genuinely open domination near evaluation (can depend on U period in this part).
structure Meristem (U : E → α → F) (x : E) (μ : Measure α) (k : ℕ) : Prop where
  haveSmooth : ∃ S ∈ 𝓝 x, (∀ᵐ a ∂μ,∀ y∈S, ContDiffAt ℝ (↑k) (fun x=>U x a) y) ∧
    (∀ i≤k, ∃ v : α→ℝ, Integrable v μ ∧ (∀ y∈S, AEStronglyMeasurable (JetF U i y) μ) ∧
      ∀ᵐ a ∂μ, ∀ y∈ S,‖JetF U i y a‖ ≤ v a)

namespace Meristem
variable (p : Meristem U x μ k)
include p
variable [CompleteSpace F]
lemma calls : let f x:=∫ i,U x i ∂μ
    ContDiffAt ℝ (↑k) f x ∧ ∀ i≤k,Integrable (JetF U i x) μ ∧ (iteratedFDeriv ℝ i f x)= ∫ a, JetF U i x a ∂μ := by
  intro f
  obtain ⟨S,hS,hh,hp⟩:= p.haveSmooth
  obtain ⟨T,hT,h,t⟩:= mem_nhds_iff.mp hS
  let g (i : ℕ) x := ∫ a,JetF U i x a ∂μ
  have he i (hi:i≤k) (x) (hx:x∈T) : Integrable (JetF U i x) μ := by
    obtain ⟨v,hH,hv,hU⟩:= hp i hi
    exact hH.mono' (hv _ (hT hx)) (hU.mono fun a h=> h _ (hT hx))
  have hV i (hi:i≤k) x (hx:x∈T) : ContinuousAt (g i) x := by
    obtain ⟨v,hH,hv,hU⟩:= hp i hi
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence v
      ?_ ?_ hH ?_
    · filter_upwards [h.mem_nhds hx] with y hy; exact hv _ (hT hy)
    · filter_upwards [h.mem_nhds hx] with y hy; exact hU.mono fun a h=> h _ (hT hy)
    exact hh.mono fun a h=> (h _ (hT hx)).continuousAt_iteratedFDeriv (Nat.cast_le.mpr hi)
  let D i x := ∫ a, fderiv ℝ (fun y=>JetF U i y a) x ∂μ
  have hF i (hi:i<k) x (hx:x∈T) : HasFDerivAt (g i) (D i x) x := by
    obtain ⟨v,hH,hv,hU⟩:= hp (i+1) hi
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=JetF U i) (bound:=v)
      (F':=fun x a=>fderiv ℝ (fun y=>JetF U i y a) x) (h.mem_nhds hx) _ (he i hi.le _ hx) _ _ hH
    · filter_upwards [hh] with a ha x hs
      exact ((ha x (hT hs)).differentiableAt_iteratedFDeriv (m:=i) (Nat.cast_lt.mpr hi)).hasFDerivAt
    · filter_upwards [h.mem_nhds hx] with x hx; exact (he _ hi.le _ hx).1
    · let e := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i+1)=> E) F
      have hQ a : fderiv ℝ (fun y=>JetF U i y a) x=e (JetF U (i+1) x a) := congr_fun
        (fderiv_iteratedFDeriv (𝕜:=ℝ) (f:=fun y=>U y a) (n:=i)) x
      simp_rw [hQ]
      exact e.continuous.comp_aestronglyMeasurable (hv _ (hT hx))
    filter_upwards [hU] with a ha x hs; exact (norm_fderiv_iteratedFDeriv (𝕜:=ℝ) (f:=fun y=> U y a)).trans_le (ha _ (hT hs))
  have hq i (hi:i≤k) : ∀ y∈T, iteratedFDeriv ℝ i f y=g i y := by
    induction i with
    | zero =>
      intro z hz
      rw [iteratedFDeriv_zero_eq_comp]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toLinearIsometry.integral_comp_comm (μ:=μ) (U z)).symm
    | succ i ih =>
      intro y hy
      have he' : g i =ᶠ[𝓝 y] iteratedFDeriv ℝ i f := by filter_upwards [h.mem_nhds hy] with z hz using (ih (by omega) z hz).symm
      rw [iteratedFDeriv_succ_eq_comp_left, comp_apply, ((hF i hi y hy).congr_of_eventuallyEq he'.symm).fderiv]
      let e : (E →L[ℝ] (E [×i]→L[ℝ] F)) ≃ₗᵢ[ℝ] (E [× (i+1)]→L[ℝ] F) := (continuousMultilinearCurryLeftEquiv ℝ (fun _: Fin (i+1)=>E) F).symm
      have hs:= LinearIsometry.integral_comp_comm (𝕜:=ℝ) (F:=E [×(i+1)]→L[ℝ] F) (E:=E→L[ℝ] (E [×i]→L[ℝ] F)) (μ:=μ) (show _ from e.toLinearIsometry)
        (fun a=> fderiv ℝ (fun y=> JetF U i y a) y)
      exact hs.symm
  refine ⟨?_,fun i hi=> ⟨he _ hi _ t,hq i hi _ t⟩⟩
  refine ContDiffOn.contDiffAt ?_ (h.mem_nhds t)
  have hx i : ∀ x∈T, iteratedFDerivWithin ℝ i f T x=iteratedFDeriv ℝ i f x := fun x hx=> iteratedFDerivWithin_of_isOpen i h hx
  refine (contDiffOn_nat_iff_continuousOn_differentiableOn h.uniqueDiffOn).2 ⟨fun i hi=> ?_,fun i hi =>?_⟩
  · refine ContinuousOn.congr (show ContinuousOn (g i) T from fun x hx => (hV i hi x hx).continuousWithinAt) (fun x' hv=>?_)
    exact (hx i _ hv).trans (hq i hi _ hv)
  refine DifferentiableOn.congr (show DifferentiableOn ℝ (g i) T from fun x hx=> (hF i hi x hx).differentiableAt.differentiableWithinAt) (fun x hx'=>?_)
  exact (hx i _ hx').trans (hq _ hi.le _ hx')

lemma buds {D v : ℝ} (f : α → ℝ) (hf : Integrable f μ) (hd : 0 ≤ D)
    (hg : ∫ a,f a ∂μ ≤ v) (hp : ∀ᵐ a ∂μ, Brush k (f a) D (fun x=> U x a) x) :
    Brush k v D (fun x=> ∫ a,U x a ∂μ) x := by
  have hs:=p.calls
  refine ⟨hs.1,hd,fun i hi=> ?_⟩
  unfold normJ; rw [(hs.2 i hi).2]; apply (norm_integral_le_integral_norm _).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right hg (pow_nonneg hd i))
  rw [← MeasureTheory.integral_mul_const]; exact integral_mono_ae ((hs.2 i hi).1.norm) (hf.mul_const _) (hp.mono fun a h=> h.order i hi)
end Meristem
end YM.ConnectedActivityE6.Blaze
