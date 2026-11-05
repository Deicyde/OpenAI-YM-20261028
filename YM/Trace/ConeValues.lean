import YM.Trace.Weight
import YM.Mink.Geometry

/-! Strict-time slice estimates and the cone-positive Fourier sign convention. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace YM.Trace
open Function MeasureTheory Set Filter Boundary Complex
open scoped Topology BigOperators ENNReal ContDiff

lemma Growth.finite_compacts {X : Type*} [NormedAddCommGroup X] [MeasurableSpace X] [BorelSpace X] {μ : Measure X}
    {A : ℝ≥0∞} {n : ℕ} (h : Growth μ A n) (ha : A ≠ ⊤) : IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun k hk => ?_⟩
  obtain ⟨r,hr⟩ := Metric.isBounded_iff_subset_closedBall 0 |>.mp hk.isBounded
  exact measure_mono (hr.trans (Metric.closedBall_subset_closedBall (le_max_right 1 r))) |>.trans
     (h (max 1 r) (le_max_left ..)) |>.trans_lt (ENNReal.mul_lt_top ha.lt_top (by finiteness))
lemma Tempered.finite_compacts {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} (h : Tempered μ) : IsFiniteMeasureOnCompacts μ := by
  obtain ⟨n,A,h⟩ := h; exact h.finite_compacts (by finiteness)

theorem norm_le_cone {x : E4} (hp : x∈ Mink.cone) : ‖x‖ ≤ 2*time x := by
  have h : ‖spatial x‖ ≤ time x := hp
  nlinarith [norm_nonneg x,norm_nonneg (spatial x),Mink.squares x]
lemma norm_time (x : E4) : |time x| ≤ ‖x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]; rw [sq_abs,Mink.squares]; exact le_add_of_nonneg_left (by positivity)

theorem exp_strip {b : ℝ} (hb : 0 < b) (k : ℕ) : ∃ s : ℝ, 0≤s ∧ ∀ q : ℝ, 0≤q → ∀ p∈Mink.cone,
    ‖p‖ ≤ q → q ≤ 2*time p → (1+q)^k * Real.exp (-b *(time p)) ≤ s := by
  have ht := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k:ℝ) (b/2) (half_pos hb)
  simp_rw [Real.rpow_natCast] at ht
  obtain ⟨r,hr⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds one_pos)); let c:=max 1 r
  obtain ⟨d,hd⟩: BddAbove ((fun q : ℝ => (1+q)^k * Real.exp (-(b/2)*q)) '' Icc 0 c) := isCompact_Icc.bddAbove_image
     (by fun_prop)
  refine ⟨max (2^k) d, le_max_of_le_left (by positivity),fun q hq p hp hx hh => ?_⟩
  have he : -(b)*time p ≤ -(b/2)*q := by nlinarith
  by_cases hc : c≤q
  · calc _ ≤ (2*q)^k * Real.exp (-b/2 * q) := by
               apply mul_le_mul (by gcongr; linarith [le_max_left 1 r]) (Real.exp_le_exp.mpr (by linarith)) (by positivity) (by positivity)
         _ = 2^k * (q^k * Real.exp (-(b/2)*q)) := by rw [neg_div,mul_pow,mul_assoc]
         _ ≤ 2^k := mul_le_of_le_one_right (by positivity) (hr _ ((le_max_right ..).trans hc)).le
         _ ≤ _ := le_max_left ..
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp_of_le he) (by positivity)).trans
    ((hd (mem_image_of_mem _ ⟨hq,(le_of_lt (lt_of_not_ge hc))⟩)).trans (le_max_right ..))

lemma exp_cost {b : ℝ} (hb : 0<b) (l : ℕ) : ∃ C : ℝ,0≤C ∧ ∀ p∈Mink.cone, (1+|time p|) * Real.exp (-b*time p) ≤ C / weight l p := by
  obtain ⟨C,hC,hs⟩ := exp_strip hb (l+1)
  refine ⟨C,hC,fun p hp => ?_⟩
  rw [le_div_iff₀ (weight_pos ..), weight]
  refine le_trans (b := _ *(1+‖p‖)^l * Real.exp _) (le_of_eq (mul_right_comm ..)) ?_
  exact (mul_le_mul_of_nonneg_right (by
    rw [pow_succ]; rw [mul_comm (1+|time p|)]; gcongr; apply norm_time) (Real.exp_nonneg _)).trans
      (hs ‖p‖ (norm_nonneg _) p hp le_rfl (norm_le_cone hp))

lemma Tempered.integrable_damp (μ : Measure E4) (h : Tempered μ) (hf : μ (Mink.coneᶜ)=0)
    {b : ℝ} (hb : 0<b) : Integrable (fun p : E4 => (1+|time p|)*Real.exp (-b*time p)) μ := by
   obtain ⟨n,A,h⟩ := h; obtain ⟨C,-,hc⟩ := exp_cost hb (n+1)
   have ht :=  ((h.integrable_weight μ ENNReal.ofReal_lt_top).const_mul C)
   refine ht.mono' (by fun_prop (disch:=first |fun_prop|exact Mink.clock_cont)) ?_
   have he : ∀ᵐ p∂μ,p∈Mink.cone := by rwa [ae_iff]
   filter_upwards [he] with p hp
   simpa [Real.norm_of_nonneg,Real.exp_nonneg,mul_nonneg, add_nonneg,abs_of_nonneg (show 0 ≤ 1+|time p| by positivity), div_eq_mul_inv] using! hc _ hp

lemma Tempered.integrable_exp (μ : Measure E4) (h : Tempered μ) (hf : μ (Mink.coneᶜ)=0) {b : ℝ} (hb : 0<b) :
    Integrable (fun p : E4 => Real.exp (-b * time p)) μ := (h.integrable_damp μ hf hb).mono' (by fun_prop (disch:=first |fun_prop|exact Mink.clock_cont))
      (.of_forall fun x => (Real.norm_of_nonneg (Real.exp_nonneg _)).trans_le (le_mul_of_one_le_left (Real.exp_nonneg _) (le_add_of_nonneg_right (abs_nonneg _))))
    -- lemma one_le_left? test
end YM.Trace
