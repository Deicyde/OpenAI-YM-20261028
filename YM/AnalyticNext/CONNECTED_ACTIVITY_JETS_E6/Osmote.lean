import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Lac
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Meristem

/-!
# Compact-parameter log branches

Integration with physical/numbered parameters. Recurrence near ORIGINAL χ
requires Healthy only at queried evaluation point but branch extension C⁴
on true neighborhoods. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function MeasureTheory Set
open scoped Topology InnerProductSpace ContDiff BigOperators Classical
variable {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]
open Brush
variable {x : E} {z : Y} {s T : Set E} {k j : ℕ} {v b : ℝ}

lemma sprains {U : E → Y → F} (hp : ContDiffAt ℝ (↑k) (uncurry U) (x,z)) :
    let L := ContinuousLinearMap.inl ℝ E Y
    JetF U k x z=(iteratedFDeriv ℝ k (uncurry U) (x,z)).compContinuousLinearMap (fun _=> L) := by
  intro L; let i : E × Y :=(0,z); let g u:= uncurry U (u+i)
  have he j : L j+i=(j,z) := by simp [L,i]
  have hx : ContDiffAt ℝ (↑k) g (L x) := ContDiffAt.comp _ (g:=uncurry U) (f:=fun x=>x+i) (by rw [he]; exact hp)
    (contDiffAt_id.add contDiffAt_const)
  unfold JetF; rw [show (fun x=>U x z)=g ∘ L from funext (fun x=> by simp [g,he]), linear_pull L hx]
  unfold g; rw [iteratedFDeriv_comp_add_right,he]

-- derive intervals with tests at all x
set_option maxHeartbeats 400000 in
lemma yoga {U : E → ℝ → F} [FiniteDimensional ℝ E]
    (h : ∀ z∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ (↑k) (uncurry U) (x,z)) :
    Meristem U x (volume.restrict (Set.Ioc 0 1)) k := by
  let T := Set.Icc (0:ℝ) 1; let V := Set.Ioc (0:ℝ) 1
  let S := {z | ContDiffAt ℝ (↑k) (uncurry U) z}
  have ht : IsOpen S := isOpen_iff_mem_nhds.mpr (fun i hi=> by exact ContDiffAt.eventually (show ContDiffAt _ _ _ _ from hi) (by simp))
  obtain ⟨s,t,hs,hP,hx,hT,hv⟩:= generalized_tube_lemma (isCompact_singleton (x:=x)) (show IsCompact T from isCompact_Icc) ht (show {x}×ˢT⊆ S from by
    rintro ⟨i,j⟩ ⟨hi,hj⟩; have hx:i=x:=mem_singleton_iff.mp hi; subst i; exact h j hj)
  obtain ⟨r,hr,H⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds (hx (mem_singleton _)))
  let C := Metric.closedBall x r; have hc : IsCompact C := isCompact_closedBall ..
  have hj (i:E) (hi:i∈ C) (j:ℝ) (hj:j∈T) : ContDiffAt ℝ (↑k) (uncurry U) (i,j) := hv (mk_mem_prod (H hi) (hT hj))
  have hh : ∀ᵐ a ∂(volume.restrict V),a∈T := (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun _ ha=> Ioc_subset_Icc_self ha
  refine ⟨C, Metric.closedBall_mem_nhds _ hr,hh.mono (fun i hi x h => (hj x h i hi).comp x (f:=fun z:E=> (z,i)) (contDiffAt_id.prodMk contDiffAt_const)),?_⟩
  intro j hJ
  have hL : ContinuousOn (fun z:E×ℝ=>JetF U j z.1 z.2) (C×ˢ T) := by
    let L := ContinuousLinearMap.inl ℝ E ℝ
    let W := ContinuousMultilinearMap.compContinuousLinearMapL (F:=F) (fun _ : Fin j => L)
    have hz : ContinuousOn (fun p=> W (iteratedFDeriv ℝ j (uncurry U) p)) (C×ˢ T) := fun ⟨x,y⟩ hi=>
      (W.continuous.continuousAt.comp ((hj x hi.1 y hi.2).continuousAt_iteratedFDeriv (Nat.cast_le.mpr hJ))).continuousWithinAt
    exact hz.congr fun ⟨x,y⟩ hi=> sprains ((hj x hi.1 y hi.2).of_le (Nat.cast_le.mpr hJ))
  obtain ⟨M,hM⟩:= (hc.prod isCompact_Icc).bddAbove_image hL.norm
  refine ⟨fun _=>M,integrable_const _, fun y hy => ?_,hh.mono (fun i hi x hx=> hM (mem_image_of_mem _ (show (x,i)∈C×ˢT from ⟨hx,hi⟩)))⟩
  have he : ContinuousOn (JetF U j y) V := hL.comp (f:=fun a:ℝ=>(y,a)) (continuous_const.prodMk continuous_id).continuousOn
    fun _ hv=> ⟨hy,Ioc_subset_Icc_self hv⟩
  exact he.aestronglyMeasurable measurableSet_Ioc

lemma yogic {U : E → ℝ → ℝ} [FiniteDimensional ℝ E]
    (h : ∀ z∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ (↑k) (uncurry U) (x,z))
    (he : ∀ i∈Set.Icc (0:ℝ) 1, Brush k b v (fun y=> U y i) x) :
    Brush k b v (fun y=>∫ z in (0:ℝ)..1,U y z) x := by
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  apply (yoga h).buds (fun _=>b) (integrable_const _) (he 0 ⟨le_rfl,zero_le_one⟩).pos
  · simp
  exact (MeasureTheory.ae_restrict_mem measurableSet_Ioc).mono fun _ hh=> he _ (Set.Ioc_subset_Icc_self hh)
end YM.ConnectedActivityE6.Blaze
