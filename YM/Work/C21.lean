import YM.Bid.Tar
import YM.Org.Twist

/-!
# Local realization of both partial boundaries
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C21
open Function Set Filter MeasureTheory Metric Boundary Boundary.Surface Probe
open scoped Topology

/-- Identify a germ with a given weak limit of interior slices. All the real arguments
(including spectators) are integrated at once. -/
lemma realize {n : ℕ} {E : Full n → ℂ} {U : Set (Full n)} {V : Set (Points n)}
    (hU : ∀ p, p ∈ U ↔ shade p ∈ V) {x y : Points n} (h : glow x y ∈ closure U)
    (A : Pane E U (glow x y)) (hc : ∀ z ∈ V, Continuous fun i => E (glow i z))
    {Q : Distn (Points n)} (hq : ∀ f : Joint n, Tendsto (fun z => ∫ i, E (glow i z) * f i)
      (𝓝[V] y) (𝓝 (Q f))) :
    ∃ r>0, ∀ f : Joint n, HasCompactSupport ⇑f → tsupport f ⊆ ball x r →
      Q f = ∫ i, A.extendF (glow i y) * f i := by
  have H : MapsTo shade U V := fun p hp => (hU p).1 hp
  haveI : (𝓝[V] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (by simpa using H.closure (cont_sh n) h)
  obtain ⟨d,hd,hA,hE⟩ := A.revive
  let C := ‖A.extendF (glow x y)‖ + 1
  have hev : ∀ᶠ q in 𝓝 (glow x y), ‖A.extendF q‖ < C :=
    A.doc.continuousAt.norm.tendsto.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp (((home n).tendsto (x,y)).eventually
    ((show ∀ᶠ q in 𝓝 (glow x y), q ∈ ball (glow x y) d from ball_mem_nhds _ hd).and hev))
  have hh {i z : Points n} (hi : i ∈ ball x r) (hz : z ∈ ball y r) :
      glow i z ∈ ball (glow x y) d ∧ ‖A.extendF (glow i z)‖ < C :=
    @hR (i,z) ((ball_prod_same x y r).le (show (i,z) ∈ ball x r ×ˢ ball y r from ⟨hi,hz⟩))
  have hk : ∀ᶠ z in 𝓝[V] y, z ∈ ball y r := Eventually.filter_mono nhdsWithin_le_nhds (ball_mem_nhds _ hr)
  have he {i z : Points n} (hi : i ∈ ball x r) (hz : z ∈ ball y r) (hv : z ∈ V) :
      A.extendF (glow i z) = E (glow i z) := hE ⟨(hh hi hz).1,(hU _).2 (by simpa using hv)⟩
  refine ⟨r, hr, fun f _ hf => tendsto_nhds_unique (hq f) ?_⟩
  apply tendsto_integral_filter_of_dominated_convergence (fun i => C * ‖f i‖)
  · filter_upwards [self_mem_nhdsWithin] with z hz using
      ((hc z hz).mul f.continuous).aestronglyMeasurable
  · filter_upwards [hk,self_mem_nhdsWithin] with z hz hv
    refine Eventually.of_forall fun i => ?_
    by_cases hp : f i = 0
    · simp [hp]
    have hi := hf (subset_tsupport _ hp)
    rw [← he hi hz hv,norm_mul]
    exact mul_le_mul_of_nonneg_right (hh hi hz).2.le (norm_nonneg _)
  · exact f.integrable.norm.const_mul C
  refine Eventually.of_forall fun i => ?_
  by_cases hp : f i = 0
  · simp [hp]
  have hi := hf (subset_tsupport _ hp)
  have hw := (hA _ (hh hi (mem_ball_self hr)).1).continuousAt
  have ht : Tendsto (fun z => A.extendF (glow i z)) (𝓝[V] y) (𝓝 (A.extendF (glow i y))) :=
    (hw.comp ((home n).comp (continuous_const.prodMk continuous_id)).continuousAt).continuousWithinAt
  exact (ht.mul tendsto_const_nhds).congr' ((hk.and self_mem_nhdsWithin).mono fun z hz =>
    show A.extendF (glow i z) * f i = E (glow i z) * f i by rw [he hi hz.1 hz.2])

lemma reindex {n : ℕ} (E : Full n → ℂ) (P : NearPair n) (f : Joint n) (z : Points n) :
    ∫ i, E (glow i (P.switch z)) * (along P.switch.toContinuousLinearEquiv f) i =
      ∫ i, (E ∘ P.name) (glow i z) * f i := by
  rw [← P.switch.measurePreserving.integral_comp P.switch.toHomeomorph.measurableEmbedding]
  have h i : P.switch (P.switch i)=i := P.switch.symm_apply_apply i
  simp only [along_at,LinearIsometryEquiv.coe_toContinuousLinearEquiv,h,comp_apply,NearPair.name,
    re_glow,im_glow]

theorem answer : YM.Bid.C21 := by
  intro G L S F Y D Z hD hF n v y P A
  constructor
  · intro x hx
    refine realize (V := fields n) (fun _ => Iff.rfl) (A.permitted.first x) (A.original x hx) (fun z hz => ?_)
      (Z.sees hF v _ A.permitted.here (hD n))
    exact (hF.hol n v).continuousOn.comp_continuous ((home n).comp (continuous_id.prodMk continuous_const))
      (fun _ => show shade (glow _ z) ∈ fields n by simpa using hz)
  intro x hx
  let V := P.switch ⁻¹' fields n
  have hV p : p ∈ P.name ⁻¹' tube n ↔ shade p ∈ V := by
    change shade (P.name p) ∈ fields n ↔ P.switch (shade p) ∈ fields n
    simp [NearPair.name]
  refine realize hV (A.permitted.second x) (A.tilted x hx) (fun z hz => ?_) (fun f => ?_)
  · have he : Continuous P.name := (home n).comp ((P.switch.continuous.comp (cont_Re n)).prodMk
      (P.switch.continuous.comp (cont_sh n)))
    exact (hF.hol n _).continuousOn.comp_continuous (he.comp ((home n).comp (continuous_id.prodMk continuous_const)))
      (fun _ => (hV _).2 (show shade (glow _ z) ∈ V by simpa using hz))
  have ht := Z.sees hF (v ∘ P.s) _ A.permitted.there (hD n) (along P.switch.toContinuousLinearEquiv f)
  have hP : Tendsto P.switch (𝓝[V] dawn y) (𝓝[fields n] P.switch (dawn y)) :=
    P.switch.continuous.continuousWithinAt.tendsto_nhdsWithin fun _ h => h
  exact (ht.comp hP).congr' (Eventually.of_forall (reindex (Z.emit (v ∘ P.s)) P f))
end YM.Work.C21
