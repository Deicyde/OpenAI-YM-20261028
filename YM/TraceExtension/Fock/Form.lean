import YM.TraceExtension.Fock.Identify

/-! Amplitudes of a purported embedding into Fock. Fix Fourier convention
by H.operator realizations (the functional in actual W). No charged mixed
temperance needed. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {m n : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m}

def readout (f : Probe E4) (x : Wavespace m) := testPlus f (forward x)
lemma readout_meas (f : Probe E4) : Measurable (readout (m:=m) f) := (testPlus f).continuous.measurable.comp measurable_forward

structure Form (F : Spec.Final C a S) (U : F.action.operators.H →ₗᵢ[ℂ] Ambient m) where
    val : Wavespace m → ℂ
    leg : Measurable val
    means (f : Probe E4) : (⇑(signal F U f) : Wavespace m → ℂ)=ᵐ[sumMeasure m] readout f * val

lemma readout_ne (p : E4) : testPlus (probe_one (Nat.ceil ‖p‖)).choose p ≠ 0 := by
    have he := (probe_one (Nat.ceil ‖p‖)).choose_spec p (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact Nat.le_ceil _))
    let f := (probe_one (Nat.ceil ‖p‖)).choose; change ‖testPlus f p‖₊ ^2=1 at he; change testPlus f p≠0; intro h; rw [h] at he; simp at he

lemma form_exists (X : Comparison F U) (h : TraceSpectrum F μ) : Nonempty (Form F U) := by
    let v (j : ℕ) := (probe_one j).choose
    have hh (x : Wavespace m) : ∃ n, readout (v n) x ≠ 0 := ⟨Nat.ceil ‖forward x‖, readout_ne _⟩
    let q (n : ℕ) (x) := signal F U (v n) x / readout (v n) x
    let val (x) := q (Nat.find (hh x)) x
    refine ⟨val,Measurable.find (fun n => Measurable.div (Lp.stronglyMeasurable (signal F U (v n))).measurable (readout_meas _)) (fun n => ?_) hh,fun f => ?_⟩
    · exact (readout_meas _ (measurableSet_singleton _)).compl
    filter_upwards [ae_all_iff.mpr (fun n => wave_compat X h f (v n))] with i hi
    have hp := hi (Nat.find (hh i))
    rw [Pi.mul_apply]; unfold val q
    rw [← mul_div_assoc]
    apply (eq_div_iff (Nat.find_spec (hh i))).2
    rw [mul_comm]; exact hp

namespace Form
variable (Y : Form F U)
def rent (p : Wavespace m) := ‖Y.val p‖ₑ ^ 2
lemma rent_meas : Measurable Y.rent := by unfold rent; exact (Y.leg.enorm).pow_const _
def costs := (sumMeasure m).withDensity Y.rent
lemma recovered (X : Comparison F U) (h : TraceSpectrum F μ) (f : Probe E4) :
    μ.withDensity (fun p => (probeWeight f p : ℝ≥0∞)) = ((sumMeasure m).withDensity
      (Y.rent * fun x : Wavespace m => (probeWeight f (forward x):ℝ≥0∞))).map forward := by
    rw [← h.core, push_norm X]; change (modulus (signal F U f)).map _=_; congr 1; apply withDensity_congr_ae
    filter_upwards [Y.means f] with i hi; unfold rent; rw [Pi.mul_apply,hi]
    simp only [Pi.mul_apply,readout,nnnorm_mul, ENNReal.coe_mul,mul_pow,probeWeight,ENNReal.coe_pow,enorm_eq_nnnorm,mul_comm]
lemma recognized (X : Comparison F U) (h : TraceSpectrum F μ) : μ = Y.costs.map forward := by
    apply weights_injective; intro f
    rw [recovered Y X h f]; unfold costs
    rw [withDensity_mul (sumMeasure m) (rent_meas Y) (g := fun x => (probeWeight f (forward x):ℝ≥0∞)) ((probe_meas f).comp measurable_forward)]
    ext A hA
    rw [map_apply measurable_forward hA, withDensity_apply _ hA,setLIntegral_map hA (probe_meas f) measurable_forward,withDensity_apply _ (measurable_forward hA)]

lemma recognize_terms (X : Comparison F U) (h : TraceSpectrum F μ) {V : Set E4} (hv : MeasurableSet V) :
    μ V=∑' (i : Index m), ∫⁻ k in {k | totalMomentum k∈V}, Y.rent (insertP i k) ∂photons i.1 := by
    rw [recognized Y X h,map_apply measurable_forward hv,costs, sumMeasure,
        withDensity_sum,Measure.sum_apply _ (measurable_forward hv)]
    congr! 1; ext1 i
    rw [withDensity_apply _ (measurable_forward hv), setLIntegral_map (measurable_forward hv) (rent_meas Y) (embedP i).measurable]
    rfl
end Form
end YM.TraceExtension.Photons
