import YM.TraceExtension.Fock.Space
import YM.TraceExtension.Relative

/-! One particle test vectors and the coherent vector. The explicit
orthogonal projection in `polarization` is that for *real spatial
momentum*, acting complex linearly on waves (entry formula). -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical

abbrev TestList (m : ℕ) := Label m → Probe E4

def polarization (p : Space3) (j k : SpaceAxis) : ℂ :=
    ifk j k - (((p j * p k / ‖p‖^2:ℝ)):ℂ)
  where ifk (j k : SpaceAxis) : ℂ := if j=k then 1 else 0
lemma pol_symm (p : Space3) (j k) : polarization p j k=polarization p k j := by simp [polarization,polarization.ifk,eq_comm,mul_comm]
lemma pol_real (p : Space3) (j k) : star (polarization p j k)=polarization p j k := by
    unfold polarization polarization.ifk; split_ifs <;> simp only [star_sub,star_one,star_zero,Complex.star_def,Complex.conj_ofReal]
lemma pol_bound (p : Space3) (j k) : ‖polarization p j k‖≤ 2 := by
    apply (norm_sub_le ..).trans
    refine le_trans (add_le_add (show ‖polarization.ifk j k‖≤1 by unfold polarization.ifk; split <;> simp) (show ‖(_ : ℂ)‖≤1 from ?_)) (by norm_num)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_div, abs_of_nonneg (sq_nonneg ‖p‖),abs_mul]
    by_cases h:p=0
    · simp [h]
    apply (div_le_one (by positivity : (0:ℝ)<‖p‖^2)).2
    rw [pow_two]; exact mul_le_mul (PiLp.norm_apply_le p j) (PiLp.norm_apply_le p k) (abs_nonneg _) (norm_nonneg _)
lemma pol_meas (j k) : Measurable (fun x => polarization x j k) := by unfold polarization; fun_prop

variable {m n : ℕ}

def rawPhoton (h : TestList m) (j : Label m) (p : Space3) : ℂ := ‖p‖ • testPlus (h j) (momentum p)
def testPhoton (h : TestList m) (j : Label m) (p : Space3) : ℂ := ∑ i : SpaceAxis,
    polarization p j.2 i * rawPhoton h (j.1,i) p

lemma rawPhoton_add (h g : TestList m) (j p) : rawPhoton (h+g) j p=rawPhoton h j p+rawPhoton g j p := by
    simp [rawPhoton, map_add, smul_add]
lemma rawPhoton_smul (h : TestList m) (c : ℂ) (j p) : rawPhoton (c • h) j p=c*rawPhoton h j p := by
    unfold rawPhoton; rw [Pi.smul_apply,map_smul,_root_.smul_apply,mul_smul_comm,smul_eq_mul]
lemma photon_add (h g : TestList m) (j p) : testPhoton (h+g) j p=testPhoton h j p+testPhoton g j p := by
    simp [testPhoton,rawPhoton_add,mul_add,Finset.sum_add_distrib]
lemma photon_smul (h : TestList m) (c : ℂ) (j p) : testPhoton (c•h) j p=c*testPhoton h j p := by
    unfold testPhoton; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by rw [rawPhoton_smul,mul_left_comm]
lemma testPhoton_meas (h : TestList m) (j : Label m) : Measurable (testPhoton h j) :=
    Finset.measurable_sum _ fun i _ => (pol_meas ..).mul (by unfold rawPhoton; fun_prop)
lemma raw_lp (h : TestList m) (j : Label m) : MemLp (rawPhoton h j) 2 photon := by
    let f := testPlus (h j)
    obtain ⟨C,hC,hf⟩ := schwartz_bound f 4
    have he (x : Space3) : ‖rawPhoton h j x‖ ≤ C * ((1+‖x‖)^3)⁻¹ := by
        change ‖‖x‖ • f (momentum x)‖ ≤ _
        rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
        have hx : ‖x‖≤‖momentum x‖ := by
            have hu := Mink.squares (momentum x)
            rw [momentum_energy,momentum_space] at hu; nlinarith [norm_nonneg (momentum x)]
        calc
          _ ≤ (1+‖x‖) * (C * ((1+‖momentum x‖)^4)⁻¹) := mul_le_mul (by linarith) (hf _) (norm_nonneg _) (by positivity)
          _ ≤ (1+‖x‖) * (C * ((1+‖x‖)^4)⁻¹) := by gcongr
          _ = _ := by field_simp
    have hp : Measurable (rawPhoton h j) := by unfold rawPhoton; fun_prop
    refine (memLp_norm_iff hp.aestronglyMeasurable).1 ((memLp_two_iff_integrable_sq hp.aestronglyMeasurable.norm).2 ?_)
    have hx := inverse_integrable (μ:=photon) (A:=Real.pi) (k:=2) Real.pi_pos.le (fun R hr => (photon_ball (zero_lt_one.trans_le hr)).le)
    apply (hx.const_mul (C^2)).mono' (hp.norm.pow_const _).aestronglyMeasurable
    filter_upwards with x
    change ‖(‖rawPhoton h j x‖)^2‖ ≤ C^2 * ((1+‖x‖)^3)⁻¹
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    refine (pow_le_pow_left₀ (norm_nonneg _) (he x) 2).trans ?_
    rw [mul_pow]; apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); rw [pow_two]; exact mul_le_of_le_one_right (by positivity) (inv_le_one_of_one_le₀ (by exact one_le_pow₀ (by simp)))

lemma testPhoton_lp (h : TestList m) (j : Label m) : MemLp (testPhoton h j) 2 photon := by
    unfold testPhoton; apply memLp_finsetSum
    intro i _
    apply ((raw_lp h (j.1,i)).const_mul (2:ℂ)).mono ((pol_meas ..).aestronglyMeasurable.mul (raw_lp h (j.1,i)).1)
    filter_upwards with p
    simp only [Pi.mul_apply,norm_mul]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); simpa using pol_bound p j.2 i

/-- squared norm of the Maxwell electric test -/
def qnorm (h : TestList m) := ∑ j : Label m, ∫ p, ‖testPhoton h j p‖ ^ 2 ∂photon
lemma qnorm_nonneg (h : TestList m) : 0 ≤ qnorm h := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

def pureTest (h : Fin n → TestList m) (i : Tags m n) (p : Mom n) := ∏ k, testPhoton (h k) (i k) (p k)
lemma pureTest_meas (h : Fin n → TestList m) (i) : Measurable (pureTest h i) := by
    unfold pureTest; apply Finset.measurable_prod; exact fun j _ => (testPhoton_meas _ _).comp (measurable_pi_apply _)
lemma pure_norm (h : Fin n → TestList m) (i p) : ‖pureTest h i p‖^2=∏ k, ‖testPhoton (h k) (i k) (p k)‖^2 := by
    unfold pureTest; rw [norm_prod, Finset.prod_pow]
lemma pure_integral (h : Fin n → TestList m) (i) :
    (∫ p, ‖pureTest h i p‖^2 ∂photons n) = ∏ k, ∫ x, ‖testPhoton (h k) (i k) x‖^2 ∂photon := by
    simp_rw [pure_norm]; exact integral_fintype_prod_eq_prod (μ:=fun _ : Fin n => photon) (fun k x=>‖testPhoton (h k) (i k) x‖^2)
lemma pure_lp (h : Fin n → TestList m) (i) : MemLp (pureTest h i) 2 (photons n) := by
    have hp := (pureTest_meas h i).aestronglyMeasurable (μ:=photons n)
    refine (memLp_norm_iff hp).1 ((memLp_two_iff_integrable_sq hp.norm).2 ?_); simp_rw [pure_norm]
    exact Integrable.fintype_prod (μ:=fun _ : Fin n => photon) (fun k => (testPhoton_lp (h k) (i k)).norm.integrable_sq)
lemma pure_sum (h : Fin n → TestList m) :
    (∑ i : Tags m n, ∫ x, ‖pureTest h i x‖^2 ∂photons n) = ∏ k, qnorm (h k) := by
    simp_rw [pure_integral,qnorm]; exact (Fintype.prod_sum (fun k : Fin n => fun j : Label m => ∫ x, ‖testPhoton (h k) j x‖^2 ∂photon)).symm

def unweighted (h : TestList m) (s : Wavespace m) :=
    (I^s.1.1 / (↑(Real.sqrt (s.1.1.factorial:ℝ)):ℂ)) * pureTest (fun _ => h) s.1.2 s.2
lemma unweighted_lp (h : TestList m) : MemLp (unweighted h) 2 (sumMeasure m) := by
    have he (i : Index m) : Measurable (unweighted h ∘ insertP i) := (measurable_const (a:=I^i.fst / (↑(Real.sqrt (i.fst.factorial:ℝ)):ℂ))).mul (pureTest_meas (fun _ => h) i.2)
    have ht := (measurable_sector (unweighted h) he).aestronglyMeasurable (μ:=sumMeasure m)
    refine (memLp_norm_iff ht).1 ((memLp_two_iff_integrable_sq ht.norm).2 ?_)
    apply integrable_sum_measure
    · intro i
      apply (embedP i).integrable_map_iff.2
      exact ((pure_lp (fun _=>h) i.2).const_mul (I^i.fst / (↑(Real.sqrt (i.fst.factorial:ℝ)):ℂ))).norm.integrable_sq
    let F (n) (t : Tags m n) := ∫ x, ‖unweighted h (insertP ⟨n,t⟩ x)‖^2 ∂photons n
    have hh n t : F n t=((n.factorial:ℝ)⁻¹*∫ x, ‖pureTest (fun _=>h) t x‖^2 ∂photons n) := by
        unfold F unweighted; dsimp only
        simp_rw [norm_mul, mul_pow,integral_const_mul]; norm_num [norm_div, Real.sq_sqrt]
    have hx : Summable (fun i : Index m => F i.1 i.2) := by
        refine (summable_sigma_of_nonneg (fun x => show 0≤ F _ _ from integral_nonneg (fun _ => sq_nonneg _))).2 ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
        simp_rw [tsum_fintype, hh, ← Finset.mul_sum, pure_sum]; simpa [div_eq_mul_inv,mul_comm] using Real.summable_pow_div_factorial (qnorm h)
    refine hx.congr ?_
    rintro ⟨i,t⟩
    rw [(embedP (m:=m) ⟨i,t⟩).integral_map]; simp [F]

def bareCoherent (h : TestList m) : Ambient m := (unweighted_lp h).toLp (unweighted h)
def coherent (h : TestList m) : Ambient m := (↑(Real.exp (-qnorm h/2)):ℂ) • bareCoherent h
/-- At zero test this is just sector zero. -/
def vacuum (m : ℕ) : Ambient m := coherent 0
end YM.TraceExtension.Photons
