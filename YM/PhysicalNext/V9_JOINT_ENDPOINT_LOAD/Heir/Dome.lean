import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata

/-! # Compact-profile common neighborhoods for finite-order `Covered` -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Set Function Filter Metric MeasureTheory Planned.AtomRegular
open scoped Topology ContDiff BigOperators Classical
variable {E F Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  {n j : ℕ} {f : Z → E → F}

def docked (f : Z → E → F) (j : ℕ) (y : E × Z) := iteratedFDeriv ℝ j (f y.2) y.1
private def casts (E Z : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup Z] [NormedSpace ℝ Z] (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) :=
  ContinuousMultilinearMap.compContinuousLinearMapL (𝕜:=ℝ) (E:=fun _ => E) (E₁:=fun _ => E × Z) (F:=F) (fun _ : Fin j => ContinuousLinearMap.inl ℝ E Z)
private lemma docked_eq {x : E × Z} (h : ContDiffAt ℝ n (fun p : E × Z => f p.2 p.1) x) (hj : j ≤ n) :
    docked f j x=casts E Z F j (iteratedFDeriv ℝ j (fun p : E × Z => f p.2 p.1) x) := by
  let L := ContinuousLinearMap.inl ℝ E Z
  let g (y : E × Z) := f y.2 y.1
  let G (y : E × Z) := g ((0,x.2)+y)
  have he : (0,x.2)+L x.1=x := by simp [L]
  have hG : ContDiffAt ℝ j G (L x.1) := (he.symm ▸ h.of_le (Nat.cast_le.mpr hj)).comp (f:=fun y => (0,x.2)+y) _ (contDiffAt_const.add contDiffAt_id)
  rw [docked,show f x.2 = G ∘ L from funext (fun i => by simp [G,g,L]),Push.Uniform.iter_lin_at hG]; unfold G; rw [iteratedFDeriv_comp_add_left,he]; rfl
lemma docked_cont {x : E × Z} (h : ContDiffAt ℝ n (fun p : E × Z => f p.2 p.1) x) (hj : j ≤ n) : ContinuousAt (docked f j) x :=
    ((casts E Z F j).continuous.continuousAt.comp (f:=iteratedFDeriv ℝ j (fun p : E × Z => f p.2 p.1)) (h.continuousAt_iteratedFDeriv (Nat.cast_le.mpr hj))).congr
      ((h.eventually (by simp)).mono fun _ hy => (docked_eq hy hj).symm)

lemma domeCovered [ProperSpace E] [MeasurableSpace Z] [OpensMeasurableSpace Z] [SecondCountableTopology Z] {μ : Measure Z}
    [IsFiniteMeasure μ] {K : Set Z} (hK : IsCompact K) (he : ∀ z∉K, f z = 0) {x : E} (hh : ∀ z∈K, ContDiffAt ℝ n (fun p : E × Z => f p.2 p.1) (x,z)) :
    Covered μ f n x := by
  let u := {p : E × Z | ContDiffAt ℝ n (fun q : E × Z => f q.2 q.1) p}
  have hu : IsOpen u := isOpen_iff_mem_nhds.mpr fun p hp => (show ContDiffAt ℝ n (fun q => f q.2 q.1) p from hp).eventually (by simp)
  have hx : ({x}:Set E) ×ˢ K ⊆ u := by rintro ⟨_,_⟩ ⟨hx,hK⟩; obtain rfl : _ = x := mem_singleton_iff.mp hx; exact hh _ hK
  obtain ⟨a,b,ha,hb,ha',hb',he'⟩ := generalized_tube_lemma isCompact_singleton hK hu hx
  have h' : a ×ˢ (univ : Set Z) ⊆ u := by
    rintro ⟨y,z⟩ ⟨hy,-⟩; by_cases hz : z ∈ K; exact he' ⟨hy,hb' hz⟩
    change ContDiffAt ℝ n _ _; refine ContDiffAt.congr_of_eventuallyEq (f:=fun _ : E × Z => (0:F)) contDiffAt_const
      ((show ∀ᶠ p in 𝓝 (y,z), p.2∉K from (hK.isClosed.isOpen_compl.preimage (continuous_snd (X:=E))).mem_nhds hz).mono (fun p hp => ?_))
    exact congr_fun (he p.2 hp) _
  obtain ⟨r,hr,h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (ha.mem_nhds (ha' (mem_singleton _)))
  choose! C hC using fun j : ℕ => fun hj : j ≤ n => show ∃ c, ∀ p∈closedBall x r ×ˢ K, ‖docked f j p‖ ≤ c from
    ((isCompact_closedBall ..).prod hK).exists_bound_of_continuousOn (fun p hp => (docked_cont (h' ⟨h hp.1, mem_univ _⟩) hj).continuousWithinAt)
  let M := ∑ j ∈ Finset.range (n+1),|C j|
  refine ⟨ball x r, isOpen_ball, mem_ball_self hr, (fun _ => M),⟨Eventually.of_forall fun z y hy => ?_,fun j hj y hy => ?_,integrable_const _,Eventually.of_forall fun z y hy j hj => ?_⟩⟩
  · exact (show ContDiffAt ℝ n (fun q => f q.2 q.1) (y,z) from h' ⟨h (ball_subset_closedBall hy), mem_univ z⟩).comp (f:=fun i => (i,z)) _ (contDiffAt_id.prodMk contDiffAt_const)
  · exact (continuous_iff_continuousAt.mpr fun z : Z => (docked_cont (h' ⟨h (ball_subset_closedBall hy),mem_univ z⟩) hj).comp (f:=fun z : Z => (y,z)) (continuousAt_const.prodMk continuousAt_id)).aestronglyMeasurable
  by_cases hz : z ∈ K
  · exact (hC j hj (y,z) ⟨ball_subset_closedBall hy,hz⟩).trans ((le_abs_self _).trans (Finset.single_le_sum (s:=Finset.range _) (f:=fun j => |C j|) (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))))
  rw [he z hz]; cases j with
  | zero => rw [norm_iteratedFDeriv_zero,Pi.zero_apply,norm_zero]; unfold M; positivity
  | succ j => rw [show iteratedFDeriv ℝ (j+1) (0:E→F) y=0 from congr_fun (iteratedFDeriv_const_of_ne (c:=(0:F)) (n:=j+1) (by omega) (𝕜:=ℝ)) (a:=y),norm_zero]; unfold M; positivity
end YM.PhysicalNext.JointLoad.Heir
