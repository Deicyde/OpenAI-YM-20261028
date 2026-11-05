import YM.Trace.Schwartz
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
namespace YM.Trace
open Boundary Function Filter MeasureTheory Set Complex
open scoped Topology BigOperators ENNReal NNReal InnerProductSpace
set_option linter.unusedSectionVars false
variable {V : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]

/-- A uniform locally finite mass estimate, in ennreal to retain finiteness. -/
def Growth (μ : Measure V) (A : ℝ≥0∞) (n : ℕ) : Prop := ∀ r : ℝ, 1 ≤ r →
    μ (Metric.closedBall 0 r) ≤ A*(ENNReal.ofReal r)^n

def coverBand (i : ℕ) : Set V := {p | (2:ℝ)^i ≤ 1+‖p‖ ∧ 1+‖p‖ ≤ (2:ℝ)^(i+1)}
lemma bands_open_closed (i : ℕ) : MeasurableSet (coverBand (V:=V) i) := by
  change MeasurableSet ({p:V | _ ≤ (1+‖p‖)} ∩ {p:V | 1+‖p‖ ≤ _})
  refine MeasurableSet.inter (measurableSet_le (by fun_prop) (by fun_prop)) (measurableSet_le (by fun_prop) (by fun_prop))
lemma cover_bands : (⋃ i, coverBand (V:=V) i) = univ := Subset.antisymm (subset_univ _) (fun p _ => by
  obtain ⟨i,hi,hK⟩ := exists_nat_pow_near (x:=1+‖p‖) (y:=2) (by linarith [norm_nonneg p]) (by norm_num)
  exact mem_iUnion.mpr ⟨i,hi,hK.le⟩)

def weight (k : ℕ) (x : V) := (1+‖x‖)^k
lemma weight_pos (k : ℕ) (x : V) : 0<weight k x := pow_pos (by linarith [norm_nonneg x]) _

set_option maxHeartbeats 1500000
lemma Growth.band (μ : Measure V) (A : ℝ≥0∞) (n : ℕ) (hg : Growth μ A n) (i : ℕ) :
    (∫⁻ x in coverBand i, ENNReal.ofReal ((weight (n+1) x)⁻¹) ∂μ) ≤ (A*2^n) * (2⁻¹)^i := by
  let c := (2:ℝ)^i; let c' := (2:ℝ≥0∞)^i
  have hc : 1 ≤ c := one_le_pow₀ (by norm_num)
  have hv : μ (coverBand i) ≤ A*(2*c')^n := by
    rw [show (2:ℝ≥0∞)*c'=ENNReal.ofReal (2*c) by norm_num [c,c',ENNReal.ofReal_mul,ENNReal.ofReal_pow]]
    refine (measure_mono (t:=Metric.closedBall 0 (2*c)) ?_).trans (hg (2*c) (by linarith))
    intro x hx
    have hy := hx.2; rw [pow_succ] at hy; exact Metric.mem_closedBall.mpr (by rw [dist_zero_right]; linarith)
  calc
    _ ≤ ∫⁻ _ in coverBand i, ENNReal.ofReal ((c^(n+1))⁻¹) ∂μ := lintegral_mono_ae ?_
    _ ≤ _ := ?_
  · filter_upwards [ae_restrict_mem (bands_open_closed (V:=V) i)] with x hx
    apply ENNReal.ofReal_le_ofReal
    have hy : c ≤ 1+‖x‖ := hx.1
    exact (inv_le_inv₀ (weight_pos _ _) (by positivity)).2 (pow_le_pow_left₀ (by positivity) hy _)
  calc
    _ = (c'^(n+1))⁻¹ * μ (coverBand i) := by
       rw [setLIntegral_const]
       rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (show 0≤c by positivity)]
       norm_num [c',c,ENNReal.ofReal_pow]
    _ ≤ (c'^(n+1))⁻¹ * (A*(2*c')^n) := by gcongr
    _ = _ := by
      rw [pow_succ, ENNReal.mul_inv (Or.inr (by simp [c'])) (Or.inl (by simp [c'])),
         show (c'^n)⁻¹*(c')⁻¹*(A*(2*c')^n) = A*2^n*((c'^n)⁻¹ * c'^n) * (c')⁻¹ by ring,
         ENNReal.inv_mul_cancel (by simp [c']) (by simp [c'])]
      rw [mul_one]; exact congr_arg _ ENNReal.inv_pow
lemma Growth.total_weight (μ : Measure V) (A : ℝ≥0∞) (n : ℕ) (hg : Growth μ A n) :
    (∫⁻ x, ENNReal.ofReal ((weight (n+1) x)⁻¹) ∂μ) ≤ 2^(n+1)*A := by
  have he := lintegral_iUnion_le (μ:=μ) coverBand (fun x => ENNReal.ofReal ((weight (n+1) x)⁻¹))
  rw [cover_bands, Measure.restrict_univ] at he
  refine (he.trans (ENNReal.tsum_le_tsum (hg.band μ A n))).trans_eq ?_
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two,pow_succ]; ring

lemma Growth.integrable_weight (μ : Measure V) {A : ℝ≥0∞} {n : ℕ} (hg : Growth μ A n) (ha : A < ∞) :
    Integrable (fun p:V => (weight (n+1) p)⁻¹) μ := by
  refine ⟨by unfold weight; fun_prop, hasFiniteIntegral_iff_norm .. |>.mpr ?_⟩
  have hx (x : V) := Real.norm_of_nonneg (show 0 ≤ (weight (n+1) x)⁻¹ from inv_nonneg.mpr (weight_pos _ _).le)
  simp_rw [hx]
  exact (hg.total_weight μ _ _).trans_lt (ENNReal.mul_lt_top (by finiteness) ha)

variable [InnerProductSpace ℝ V]

def orderCost (f : Probe V) (j : ℕ) := (Probe.size 0 0 f + Probe.size j 0 f)
lemma orderCost_nonneg (f : Probe V) (j : ℕ) : 0≤orderCost f j := add_nonneg (apply_nonneg ..) (apply_nonneg ..)
lemma continuous_orderCost (j) : Continuous (fun f : Probe V => orderCost f j) := by
  exact (Probe.cont_size ..).add (Probe.cont_size ..)
lemma weighted_test (f : Probe V) (j : ℕ) (x : V) : ‖f x‖ ≤ orderCost f j * 2^j * (weight j x)⁻¹ := by
  have h (i) : ‖x‖^i * ‖f x‖ ≤ Probe.size i 0 f := by
    simpa only [norm_iteratedFDeriv_zero] using SchwartzMap.le_seminorm ℂ i 0 f x
  rw [← div_eq_mul_inv, le_div_iff₀ (weight_pos _ _),mul_comm ‖f x‖]
  by_cases hr : ‖x‖≤1
  · refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (a:=1+‖x‖) (by positivity) (b:=2) (by linarith) j)
       (norm_nonneg _)).trans ?_
    rw [mul_comm]
    gcongr
    exact (show ‖f x‖≤ Probe.size 0 0 _ by simpa using h 0).trans (le_add_of_nonneg_right (apply_nonneg ..))
  have hr' (i k) : 0 ≤ Probe.size i k f := apply_nonneg ..
  calc
    _ ≤ (‖x‖*2)^j * ‖f x‖ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (a:=1+‖x‖) (by positivity)
       (by linarith) j) (norm_nonneg _)
    _ = (‖x‖^j * ‖f x‖) * 2^j := by ring
    _ ≤ _ := by unfold orderCost; gcongr; have := h j; linarith [hr' 0 0]

lemma Growth.integrable_schwartz {A : ℝ≥0∞} {n : ℕ} {μ : Measure V} (hg : Growth μ A n) (ha : A < ∞)
    (f : Probe V) : Integrable f μ :=
   ((hg.integrable_weight μ ha).const_mul _).mono' f.continuous.aestronglyMeasurable (ae_of_all _ (weighted_test _ _))

lemma Growth.integrable_prod {A : ℝ≥0∞} {n : ℕ} {μ : Measure V} (hg : Growth μ A n) (ha : A < ∞)
    (f g : Probe V) {F : Type*} [NormedAddCommGroup F] (k : V → F) (hk : AEStronglyMeasurable k μ)
    (c : ℝ) (hc : ∀ x, ‖k x‖ ≤ c * ‖f x‖ * ‖g x‖) : Integrable k μ := by
    have hu : Integrable (fun x => ‖f x‖ * (max 0 c * Probe.size 0 0 g)) μ :=
        (hg.integrable_schwartz ha f).norm.mul_const ..
    refine hu.mono' hk (.of_forall fun x => (hc x).trans ?_)
    calc _ = ‖f x‖ * (c * ‖g x‖) := by ring
         _ ≤ _ := by gcongr <;> first | exact le_max_right .. | apply SchwartzMap.norm_le_seminorm

def Tempered (μ : Measure V) := ∃ n A, Growth μ (ENNReal.ofReal A) n
lemma Tempered.integrable (μ : Measure V) (ht : Tempered μ) (f : Probe V) : Integrable f μ := by
    obtain ⟨n,A,hA⟩ := ht; exact hA.integrable_schwartz (by finiteness) _
end YM.Trace
