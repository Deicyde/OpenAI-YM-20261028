import YM.EveryPhase.Pages
/-!
Continuity of the tested Wightman boundaries on the entire spectrum, and
the unselected tempered boundary as barycenter. For passage to the boundary
we use the Taylor formula from Breath/Ridge/Osc: evaluation in terms of
*strict* values plus an integral with common dominator. No uniformity over
arity needed here. Joint, not only product tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Set Filter MeasureTheory Spec Boundary Probe Next.BOUNDARY
open scoped Topology NNReal

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F) {n : ℕ}

lemma eager (v : Fin n → S.Union) (f : Joint n) {y : Heights n} (hy : y∈east n) :
    Continuous (fun i => (L.contours i).waves.psi v y f) ∧
     (∫ i, (L.contours i).waves.psi v y f ∂F.α.space.μ)=F.B.waves.psi v y f := by
  let A i x := (L.contours i).waves.restricted v y x * f x
  have ha (x) : Continuous fun i => A i x := (strict_evaluation L x v hy).1.mul continuous_const
  have hh (i) : Continuous (A i) := (Work.C15.restricted_continuous (L.cards i).fromPhase.heat v hy).mul f.continuous
  obtain ⟨m,C₀,hC,hM⟩ := power L n v
  obtain ⟨k,hk,h⟩ := Work.C15.east_broad hy
  let g (x : Points n) := C₀*k⁻¹^m*‖f x‖
  have hg : Integrable g := f.integrable.norm.const_mul _
  have hp i x : ‖A i x‖ ≤ g x := by
    dsimp only [A,g]; rw [norm_mul]; gcongr; apply hM i y k hk h
  constructor
  · apply continuous_iff_continuousAt.mpr; intro x
    exact tendsto_integral_filter_of_dominated_convergence (F:=A) g
      (Eventually.of_forall fun i => (hh i).aestronglyMeasurable) (Eventually.of_forall fun i => ae_of_all _ (hp i)) hg
      (ae_of_all _ (fun y => (ha y).tendsto x))
  haveI := F.phase.phase.decomposition.normalized
  have he : Integrable (uncurry A) (F.α.space.μ.prod volume) := by
    apply (hg.comp_snd (μ:=F.α.space.μ)).mono
      (measurable_uncurry_of_continuous_of_measurable ha (fun i => (hh i).measurable)).aestronglyMeasurable
    refine ae_of_all _ fun ⟨i,x⟩ => le_trans (hp i x) (le_abs_self (g x))
  change (∫ i, (∫ x, A i x) ∂F.α.space.μ)=_
  rw [integral_integral_swap he, Waves.psi]
  simp only [A, integral_mul_const]; simp_rw [fun x => (strict_evaluation L x v hy).2]

lemma word_axes (i) : (L.contours i).waves.Along ∧ (L.contours i).waves.Lines := by
  obtain ⟨Y,hY,-⟩ := (L.cards i).reveals
  rw [← hY]; exact ⟨Y.shore.2,Y.shore.1⟩

lemma word_continuity (v : Fin n → S.Union) (f : Joint n) :
    Continuous fun i => (L.contours i).world.W n v f := by
  obtain ⟨m,A,hA,h⟩ := power L n v
  haveI := awaits (light n)
  have hu i : (L.contours i).world.W n v f = (L.contours i).waves.desired v m 0 f :=
    tendsto_nhds_unique ((L.cards i).corner.corner n v f) ((L.contours i).waves.storm
     (h i) (word_axes L i).1 (word_axes L i).2 0 (light _) f)
  simp_rw [hu]
  unfold Waves.desired
  apply Continuous.sub
  · unfold Waves.pol Waves.rocks
    apply continuous_finsetSum; intro a _
    exact continuous_const.mul (eager L v _ (dawns (light n) zero_lt_one)).1
  apply continuous_iff_continuousAt.mpr; intro i
  refine tendsto_integral_filter_of_dominated_convergence (F:=fun i => (L.contours i).waves.wind v m 0 f)
    (bound:=fun t : ℝ => A*weight (Waves.moves (m+1) f)) ?_ ?_ (integrable_const _ (μ:=volume.restrict (Ioc (0:ℝ) 1))) ?_
  · refine Eventually.of_forall fun i => ?_
    have ht : ContinuousOn ((L.contours i).waves.wind v m 0 f) (Ioc (0:ℝ) 1) := by
      unfold Waves.wind; apply ContinuousOn.mul; unfold Waves.coal; fun_prop
      exact ((word_axes L i).1 n v _).comp (show ContinuousOn (fun t : ℝ => 0+t • rate n) _ from by fun_prop)
        (fun _ p => dawns (light n) p.1)
    exact ht.aestronglyMeasurable measurableSet_Ioc
  · exact Eventually.of_forall fun i => ae_restrict_of_forall_mem measurableSet_Ioc
      fun t ht => (L.contours i).waves.expense m (h i) 0 (light n) f ht
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
  exact tendsto_const_nhds.mul ((eager L v _ (dawns (light n) ht.1)).1.tendsto i)

theorem barycenter (v : Fin n → S.Union) (f : Joint n) :
    (∫ i, (L.contours i).world.W n v f ∂F.α.space.μ) = F.B.world.W n v f := by
  haveI := awaits (light n)
  haveI := F.phase.phase.decomposition.normalized
  obtain ⟨m,A,hA,h⟩ := power L n v
  refine tendsto_nhds_unique_of_eventuallyEq (f:=fun y : Heights n => ∫ i, (L.contours i).waves.psi v y f ∂F.α.space.μ)
    ?_ ((onFinal F).1.corner.corner n v f) ?_
  · refine tendsto_integral_filter_of_dominated_convergence (F:=fun y i => (L.contours i).waves.psi v y f)
      (bound:=fun i => Waves.toll f A m) ?_ ?_ (integrable_const _ (μ:=F.α.space.μ))
      (ae_of_all _ (fun i => (L.cards i).corner.corner n v f))
    · filter_upwards [self_mem_nhdsWithin] with y hy using (eager L v f hy).1.aestronglyMeasurable
    filter_upwards [self_mem_nhdsWithin] with y hy
    refine ae_of_all _ fun i => ?_
    rw [← Waves.meant _ (word_axes L i).1 (word_axes L i).2 v y hy f m]
    exact (L.contours i).waves.cost (h i) y (bigger hy) f
  filter_upwards [self_mem_nhdsWithin] with y hy using (eager L v f hy).2
end YM.EveryPhase
