import YM.Compact.PVM
import YM.SNAG.Approx
import YM.SNAG.Unital
import YM.Spectral.Frequencies


/-!
# Full SNAG achieved for target convention without assuming as a theorem
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral
open Function Set Filter MeasureTheory Measure Complex Analysis Boundary Probe SNAG
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators ContDiff
variable {H : Hilbert} {X : Type*}

section push
variable {Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] (P : PVM H X)
def PVM.route (f : X → Y) (h : Measurable f) : PVM H Y where
  region s := P.region (f ⁻¹' s)
  none := P.none -- defeq?
  all := P.all
  joins ht hv := P.joins (h ht) (h hv)
  real hi := P.real (h hi)
  unites s hs hC x := by
    simp_rw [Set.preimage_iUnion]; exact P.unites _ (fun i => h (hs i)) (fun _ _ hr => (hC hr).preimage f) x
  diagonal x := map f (P.diagonal x)
  finite x := inferInstance
  at_pair hi x := by rw [map_measureReal_apply h hi]; exact P.at_pair (h hi) x
end push
section fold
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X]
  [BorelSpace X] (S : Orbit H X)

local instance : MeasurableSpace (OnePoint X) := borel _
local instance : BorelSpace (OnePoint X) := ⟨rfl⟩
private def back (p : OnePoint X) : X := p.elim 0 id
omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] in
private lemma back_meas : Measurable (back (X := X)) := by
  classical
  have hv : MeasurableEmbedding ((↑): X → OnePoint X) := OnePoint.isOpenEmbedding_coe.measurableEmbedding
  intro s hs; by_cases h : 0∈s
  · rw [show back (X := X) ⁻¹' s=((↑):X→OnePoint X) '' s ∪ {OnePoint.infty} by
      ext p; induction p using OnePoint.rec <;> simp [back, h]]
    exact (hv.measurableSet_image.mpr hs).union (measurableSet_singleton _)
  rw [show back (X := X) ⁻¹' s=((↑):X→OnePoint X) '' s by
    ext p; induction p using OnePoint.rec <;> simp [back,h]]
  exact hv.measurableSet_image.mpr hs

def Orbit.P : PVM H X := (Rep.ships (plots S)).route back back_meas

theorem Orbit.total : S.Spectrum S.P := by
  intro x b
  let A := plots S
  let μ := Rep.sees A x
  let Θ := ((↑) : X → OnePoint X)
  let B : ContDiffBump (0 : X) := ⟨1,2,by norm_num,by norm_num⟩
  let f : Probe X := (B.hasCompactSupport.comp_left (show ofReal 0=0 from rfl)).toSchwartzMap
    (ofRealCLM.contDiff.comp B.contDiff)
  have he : HasCompactSupport ⇑f := B.hasCompactSupport.comp_left (show ofReal 0=0 from rfl)
  have hf : f 0=1 := by
    change (B 0:ℂ)=1; rw [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)];rfl
  let Y (n) (b : X) := panel (wide f n) b (broad f he n)
  let F n b := (adds (Y n b) (piece ..)).val
  have hw (p : X) n b : F n b (Θ p)=plane p b * wide f n p := rfl
  have ht (b : X) :
      (∫ y in ({OnePoint.infty}ᶜ: Set (OnePoint X)), plane (back y) b ∂μ)=inner ℂ x (S.translation b x) := by
    let D : Set (OnePoint X) := {OnePoint.infty}ᶜ
    let J := D.indicator (fun y => plane (back y) b)
    have hz y : Tendsto (fun n => F n b y) atTop (𝓝 (J y)) := by
      induction y using OnePoint.rec
      · rw [show J OnePoint.infty=0 from indicator_of_notMem (by simp [D]) _]
        exact tendsto_const_nhds
      rename_i y
      change Tendsto (fun n => F n b (Θ y)) _ _
      have hb : J (y:OnePoint X)=plane y b := Set.indicator_of_mem (by simp [D]) _
      simp_rw [hw,hb]
      have hz := (focus_w y f)
      rw [hf] at hz
      simpa using (tendsto_const_nhds (x := plane y b)).mul hz
    have hI (n : ℕ) : (∫ y, F n b y ∂μ)= inner ℂ x (S.translation b (send S (wide f n) x)) := by
      rw [Rep.pairings]
      change inner ℂ x (plots S (adds (Y n b) _).val x)=_
      rw [focuses, ← show _ from (swing S (w := Y n b) (f := wide f n) b (fun _ => rfl)),ContinuousLinearMap.comp_apply]
    rw [← integral_indicator (MeasurableSet.compl (measurableSet_singleton _))]
    have hvv : IsFiniteMeasure μ := Rep.fin ..
    have hh : Tendsto (fun n => ∫ y, F n b y ∂μ) atTop (𝓝 (∫ y, J y ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence
        (bound := fun _ => 1) (fun n => (F n b).continuous.aestronglyMeasurable)
        (integrable_const _) ?_ (ae_of_all _ hz)
      intro n; refine ae_of_all _ fun y => ?_
      induction y using OnePoint.rec
      · simp [show F n b OnePoint.infty=0 from rfl]
      rename_i y
      change ‖F n b (Θ y)‖≤1
      rw [hw, norm_mul,plane_norm,one_mul,wide, along_at]
      change ‖(B _:ℂ)‖ ≤ _
      simp only [norm_real,Real.norm_eq_abs, abs_of_nonneg B.nonneg,B.le_one]
    simp_rw [hI] at hh
    exact tendsto_nhds_unique hh (tendsto_const_nhds.inner ((S.translation b).continuous.continuousAt.tendsto.comp (zooms S f hf x)))
  have hv (b : X) : (∫ y, plane (back y) b ∂μ) = inner ℂ x (S.translation b x) := by
    -- ghost atom weight zero
    have hg : μ {OnePoint.infty}=0 := by
      have hz := ht 0; rw [S.origin] at hz
      have hy : μ.real {OnePoint.infty}ᶜ= μ.real Set.univ := by
        have hy := Rep.size A x
        simp_rw [plane_zero] at hz
        simp [← ofReal_pow,← show μ= Rep.sees _ _ from rfl,← hy] at hz
        simpa [← hy] using hz
      suffices he : ({OnePoint.infty} : Set (OnePoint X))ᶜ∈ ae μ from by simpa using mem_ae_iff.mp he
      haveI : IsFiniteMeasure μ := Rep.fin ..
      apply MeasureTheory.mem_ae_iff.mpr
      simp only [compl_compl]; rw [← measureReal_eq_zero_iff (measure_ne_top _ _)]
      linarith [measureReal_add_measureReal_compl (μ := μ) (measurableSet_singleton OnePoint.infty)]
    rw [← ht b, ← setIntegral_univ]; refine setIntegral_congr_set ?_
    exact EventuallyEq.symm ((ae_eq_univ).mpr (by simp [hg]))
  change charFun (Measure.map back μ) b=_
  rw [charFun_apply, integral_map back_meas.aemeasurable (by fun_prop)]
  exact hv b
end fold
end YM.Spectral
