import YM.EveryPhase.Average
/-!
# Shell estimate
-/
set_option autoImplicit false
noncomputable section
namespace YM.EveryPhase
open Function Filter Set Spec Boundary Next.BOUNDARY Spectral Mink Probe MeasureTheory Measure
open scoped Topology NNReal ENNReal InnerProductSpace ComplexConjugate Interval
open Metric

section
variable (μ ν : Measure E4) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
local notation "A" => (fun p => charFun μ p - charFun ν (-p))

omit [IsFiniteMeasure μ] [IsFiniteMeasure ν] in
lemma averaged_bound (M : ℝ) (h : μ.real univ + ν.real univ ≤ M) (x : Space3) :
    ‖averaged A x‖ ≤ M := by
  have hh p : ‖A p‖ ≤ M := (norm_sub_le ..).trans ((add_le_add (norm_charFun_le _) (norm_charFun_le _)).trans h)
  have ht t : ‖oddTest (fun t => A (position x t)) t‖ ≤ M := by
    rw [oddTest,norm_div,norm_mul,Complex.norm_I,mul_one,show ‖(2:ℂ)‖=(2:ℝ) by simp,div_le_iff₀ (by positivity)]
    exact (norm_sub_le ..).trans ((add_le_add (hh _) (hh _)).trans_eq (mul_two M).symm)
  have hc := norm_integral_le_of_norm_le (μ:=volume.restrict (Ioc (0:ℝ) 1))
    (integrable_const _) (ae_of_all _ ht)
  unfold averaged; simpa using hc

lemma char_int (μ : Measure Space3) [IsFiniteMeasure μ] (f : Probe Space3) :
    Integrable fun x => charFun μ x * hat f x := by
  refine ((hat f).integrable.norm.const_mul (μ.real univ)).mono' ?_ (ae_of_all _ fun p => ?_)
  · exact stronglyMeasurable_charFun.aestronglyMeasurable.mul
      (SchwartzMap.continuous _).aestronglyMeasurable
  rw [norm_mul]; gcongr; exact norm_charFun_le _

/-- Costs depend only on mass bound and spatial localization of the commutator. -/
def fee (R M : ℝ) := volume.real (closedBall (0:Space3) R)* M*
    (2^3 * volume.real (closedBall (0:Space3) 1))

variable {μ ν}

def ringE (u : ℝ) := time ⁻¹' Ioc (u/2) u
lemma measurable_ring (u : ℝ) : MeasurableSet (ringE u) := measurableSet_Ioc.preimage clock_cont.measurable

theorem annulus {R M : ℝ} (hc : ∀ᵐ p ∂μ, p ∈ cone) (hd : ∀ᵐ p ∂ν, p∈cone)
    (hs : μ.real univ + ν.real univ ≤ M) {u : ℝ} (hu : u ∈ Ioc (0:ℝ) 1)
    (h : ∀ x : Space3, R < ‖x‖ → averaged A x=0) :
    μ.real (ringE u) ≤ fee R M * (Probe.pref Space3)⁻¹ * (2*Real.pi) * u^2 := by
  have he := hu.1
  have hM : 0≤M := (add_nonneg measureReal_nonneg measureReal_nonneg).trans hs
  let B : ContDiffBump (0:Space3) := ⟨u,2*u,he,by linarith⟩
  let f : Probe Space3 := (B.hasCompactSupport.comp_left (show Complex.ofReal 0=0 by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  -- Uniform pointwise bound in position space, exploiting spatial dimension three
  let K := volume.real (closedBall (0:Space3) (2*u))
  haveI : ∀ u : ℝ, IsFiniteMeasure (volume.restrict (closedBall (0:Space3) u)) := fun u =>
    isFiniteMeasure_restrict.mpr ((isCompact_closedBall _ _).measure_lt_top (μ:=volume)).ne
  have hx (x : Space3) : ‖hat f x‖ ≤ K := by
    rw [hat_eq, ← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall 0 (2*u))]; swap
    · intro p hp; change _ * (↑(B p):ℂ)=0
      have HH : p ∉ tsupport B := by rw [B.tsupport_eq]; exact hp
      simp [image_eq_zero_of_notMem_tsupport HH]
    have hB p : ‖plane p (-x) * f p‖ ≤ 1 := by
      rw [norm_mul,plane_norm,one_mul]
      change ‖Complex.ofReal (B p)‖ ≤ (1:ℝ)
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg B.nonneg] using (B.le_one (x:=p))
    exact le_trans (norm_integral_le_of_norm_le (μ:=volume.restrict (closedBall 0 (2*u)))
      (integrable_const 1) (ae_of_all _ hB)) (by simp [K])
  have hI : ‖∫ x, averaged A x * hat f x‖ ≤ fee R M * u^3 := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s:=closedBall 0 R)]; swap
    · intro p hp
      have he : R < ‖p‖ := by simpa using hp
      rw [h p he,zero_mul]
    apply le_trans (norm_integral_le_of_norm_le (μ:=volume.restrict (closedBall 0 R)) (integrable_const (M*K))
      (ae_of_all _ (fun p => show ‖averaged A p * hat f p‖ ≤ M*K by
        rw [norm_mul]; exact mul_le_mul (averaged_bound μ ν M hs p) (hx p) (norm_nonneg _) hM)))
    rw [setIntegral_const,smul_eq_mul]
    dsimp only [fee,K]; rw [Measure.addHaar_real_closedBall' volume _ (show 0≤(2*u:ℝ) by positivity),
      show Module.finrank ℝ Space3=3 from finrank_euclideanSpace_fin]
    apply le_of_eq; ring
  have hμ : ∀ᵐ p ∂μ, 0 ≤ p timeAxis := hc.mono fun _ hp => ((cone_self _).mp hp).1
  have hν : ∀ᵐ p ∂ν, 0 ≤ p timeAxis := hd.mono fun _ hp => ((cone_self _).mp hp).1
  let U := (weighted μ).map spatial
  let V := (weighted ν).map fun p => -spatial p
  let r : ℝ := ∫ x, B x ∂U
  let s : ℝ := ∫ x, B x ∂V
  have hr : 0 ≤ r := integral_nonneg fun _ => B.nonneg
  have hs : 0 ≤ s := integral_nonneg fun _ => B.nonneg
  have hP := Probe.prepos (V:=Space3)
  have hh : (Probe.pref Space3) * r ≤ fee R M * u^3 := by
    have hw : (∫ x, averaged A x * hat f x) = ↑((Probe.pref Space3)*(r+s)) := by
      simp_rw [fun x => two_average μ ν x hμ hν,add_mul]
      rw [integral_add (char_int U f) (char_int V f), wave_integral, wave_integral]
      change (pref Space3) • (∫ x, (↑(B x):ℂ) ∂U) + (pref Space3) • (∫ x,(↑(B x):ℂ) ∂V) = _
      rw [integral_complex_ofReal,integral_complex_ofReal]; simp only [Complex.real_smul]
      dsimp only [r,s]; push_cast; ring
    rw [hw, Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hI
    exact le_trans (by gcongr; simp [hs]) hI
  have hi : r = ∫ p : E4, (up p:ℝ) * B (spatial p) ∂μ := by
    unfold r U; rw [integral_map rest_cont.measurable.aemeasurable B.continuous.aestronglyMeasurable,
      weighted, integral_withDensity_eq_integral_smul up_measurable]; rfl
  rw [hi] at hh
  let g := fun p : E4 => (up p:ℝ) * B (spatial p)
  have hn (p) : 0 ≤ g p := mul_nonneg (by simp) B.nonneg
  have hb : Integrable g μ := by
    apply (integrable_const 1).mono'
    · exact up_measurable.coe_nnreal_real.aestronglyMeasurable.mul
        (B.continuous.comp rest_cont).aestronglyMeasurable
    refine ae_of_all _ fun p => ?_
    rw [Real.norm_eq_abs,abs_of_nonneg (hn _)]
    exact mul_le_one₀ (up_limit _) B.nonneg B.le_one
  let v : ℝ := u/(2 * Real.pi)
  have hm : μ.real (ringE u)*v ≤ ∫ p, g p ∂μ := by
    have hV : (∫ p in ringE u, v ∂μ) = μ.real (ringE u)*v := by simp
    rw [← hV]; apply le_trans _ (setIntegral_le_integral (s:=ringE u) hb (ae_of_all _ hn))
    apply integral_mono_ae (integrable_const _) hb.integrableOn
    filter_upwards [ae_restrict_mem (μ:=μ) (measurable_ring u),ae_restrict_of_ae hc]
      with p hp hc
    obtain ⟨hT,hU⟩ := hp
    have hK : 0 ≤ time p := le_trans (by positivity : 0≤u/2) hT.le
    have hs : spatial p ∈ closedBall (0:Space3) u := mem_closedBall.mpr
      (by simpa using (le_trans hc hU))
    dsimp only [g,up]; rw [B.one_of_mem_closedBall hs,mul_one,Real.coe_toNNReal _ (pulse_positive hK)]
    apply le_trans _ (pulse_lower ⟨hK,hU.trans hu.2⟩); unfold v; rw [← div_div]; gcongr
  let c : ℝ := μ.real (ringE u)
  have hC : pref Space3*(c*v) ≤ _ := (mul_le_mul_of_nonneg_left hm hP.le).trans hh
  change c ≤ _
  apply (mul_le_mul_iff_of_pos_right (show 0<v by unfold v; positivity)).mp
  apply (mul_le_mul_iff_of_pos_left hP).mp
  apply hC.trans_eq
  unfold v; field_simp
end

def lowE (u : ℝ) := time ⁻¹' Ioc (0:ℝ) u
lemma measurable_low (u : ℝ) : MeasurableSet (lowE u) := measurableSet_Ioc.preimage clock_cont.measurable

theorem dyadic (μ : Measure E4) [IsFiniteMeasure μ] (M : ℝ) (hM : 0≤ M)
    (h : ∀ u ∈ Ioc (0:ℝ) 1, μ.real (ringE u) ≤ M*u^2) (u : ℝ) (hu : u ∈ Ioc (0:ℝ) 1) :
    μ.real (lowE u) ≤ (2*M)*u^2 := by
  have he := hu.1
  let w (n : ℕ) := u*(2⁻¹ : ℝ)^n
  have hw n : w n ∈ Ioc 0 1 := ⟨by unfold w; positivity, mul_le_one₀ hu.2 (by positivity)
    (pow_le_one₀ (by norm_num) (by norm_num))⟩
  have hv n : μ (ringE (w n)) ≤ ENNReal.ofReal (M*u^2) * (2⁻¹ : ℝ≥0∞)^n := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
    have hh := h (w n) (hw n)
    calc
      _ ≤ ENNReal.ofReal (M*(w n)^2) := ENNReal.ofReal_le_ofReal hh
      _ ≤ ENNReal.ofReal (M*u^2*(2⁻¹ : ℝ)^n) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_assoc]; unfold w; rw [mul_pow]
        gcongr; rw [pow_two]; apply mul_le_of_le_one_left (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_ofNat]
  have hp : lowE u ⊆ ⋃ n, ringE (w n) := by
    intro x hx
    obtain ⟨i,hp,hq⟩ := exists_nat_pow_near_of_lt_one (div_pos hx.1 he) ((div_le_one he).2 hx.2)
      (by norm_num : (0:ℝ)< 2⁻¹) (by norm_num)
    refine mem_iUnion.mpr ⟨i, ?_⟩
    change w i / 2 < _ ∧ _ ≤ w i
    rw [lt_div_iff₀ he] at hp; rw [div_le_iff₀ he] at hq
    unfold w
    constructor
    · refine lt_of_eq_of_lt ?_ hp; rw [pow_succ]; ring
    simpa [mul_comm] using hq
  have hm := calc μ (lowE u) ≤ ∑' n, μ (ringE (w n)) := (measure_mono hp).trans (measure_iUnion_le _)
                  _ ≤ _ := ENNReal.tsum_le_tsum hv
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two, show ENNReal.ofReal (M*u^2)* (2:ℝ≥0∞)=ENNReal.ofReal (2*M*u^2) from by
    conv_rhs => rw [show 2*M*u^2=M*u^2*2 by ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_ofNat] ] at hm
  rw [measureReal_def]; exact (ENNReal.toReal_mono (by finiteness) hm).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}
    {F : Final C f S} (L : Almanac F)

def νletter (i : F.α.space.X) (A : SumOfWords S) :=
    (L.actors i).momentum.diagonal (stands (L.actors i).operators A)

instance (i : F.α.space.X) (A : SumOfWords S) : IsFiniteMeasure (νletter L i A) :=
    (L.actors i).momentum.finite _

lemma word_pair (v w : Sentence S) : Continuous fun i =>
    inner ℂ ((L.actors i).operators.vector v) ((L.actors i).operators.vector w) := by
  have he i := (L.actors i).operators.general (L.contours i).world (L.cores i).meets _ (L.cores i).adj v w
  simp_rw [he,L.letters]
  exact word_continuity ..

lemma sum_pair (v w : SumOfWords S) : Continuous fun i =>
    inner ℂ (stands (L.actors i).operators v) (stands (L.actors i).operators w) := by
  induction v with
  | nil => simp [stands,operator]; exact continuous_const
  | cons j v ih =>
    have hv (b : SumOfWords S) : Continuous fun i =>
        inner ℂ ((L.actors i).operators.vector j.2) (stands (L.actors i).operators b) := by
      induction b with
      | nil => simp [stands,operator]; exact continuous_const
      | cons k b ih => simp_rw [stands_cons,inner_add_right,inner_smul_right]; exact (continuous_const.mul (word_pair L j.2 k.2)).add ih
    simp_rw [stands_cons,inner_add_left,inner_smul_left]; exact (continuous_const.mul (hv w)).add ih

theorem word_bound (w : SumOfWords S) : ∃ M : ℝ, 0 ≤ M ∧ ∀ i, (νletter L i w).real univ ≤ M := by
  let p i := (νletter L i w).real univ
  have he (i) : (p i:ℂ)=inner ℂ (stands (L.actors i).operators w) (stands (L.actors i).operators w) := by
    unfold p νletter; rw [(L.actors i).momentum.at_pair MeasurableSet.univ,(L.actors i).momentum.all]; rfl
  have hp : Continuous p := by
    have hh : p = fun i => (inner ℂ _ _).re := funext fun i =>
      Eq.symm (congrArg Complex.re (he i).symm)
    rw [hh]; exact Complex.continuous_re.comp (sum_pair L w w)
  obtain ⟨M,hM⟩ := (isCompact_range hp).bddAbove
  exact ⟨max 0 M,le_max_left _ _, fun i => (hM (mem_range_self i)).trans (le_max_right _ _)⟩

theorem late (w : SumOfWords S) (h : finite w) : ∃ R : ℝ, ∀ i, ∀ x : Space3, R < ‖x‖ →
    averaged (delta (L.actors i) w) x=0 := by
  obtain ⟨R,hR⟩ := distant _ _ (fin_reverse F.action.J h) h F.action.spin
  refine ⟨R,fun i x hx => ?_⟩
  have he t (ht : |t| ≤ 1) : delta (L.actors i) w (position x t)=0 := by
    rw [comm_expect (L.cores i) F.sector.derivatives F.room.kernel.laws.toSymmetric F.phase.transport.injection]
    have hh : spacelikeWords (reverseP (L.actors i).J w) (acted (L.actors i).spin (Poincare.translation (position x t)) w) := by
      rw [L.spins,L.letters]; exact hR t ht x hx
    rw [op_comm (L.actors i).operators (L.cores i).localPairs hh,sub_self]
  refine setIntegral_eq_zero_of_forall_eq_zero (fun y hy => ?_)
  have hp : |y| ≤ 1 := by rw [abs_of_nonneg hy.1.le]; exact hy.2
  simp only [oddTest, he y hp, he (-y) (by simpa using hp), sub_self, zero_div]

theorem light_bound (w : SumOfWords S) (h : finite w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i u, u∈Ioc (0:ℝ) 1 → (νletter L i w).real (lowE u) ≤ M*u^2 := by
  obtain ⟨M,hM,hμ⟩ := word_bound L w
  obtain ⟨N,hN,hν⟩ := word_bound L (reverseP F.action.J w)
  obtain ⟨R,hR⟩ := late L w h
  let A := fee R (M+N) * (Probe.pref Space3)⁻¹ * (2*Real.pi)
  have hp : 0≤ A := by unfold A fee; have h := Probe.prepos (V:=Space3); positivity
  refine ⟨2*A,by positivity, fun i => dyadic (νletter L i w) A hp (fun u hu => ?_)⟩
  have hv x (hx : R < ‖x‖) := hR i x hx
  unfold delta at hv; rw [L.letters] at hv
  exact annulus (ν:=νletter L i (reverseP F.action.J w)) (cave (L.cores i) _) (cave (L.cores i) _)
    (add_le_add (hμ i) (hν i)) hu hv
end YM.EveryPhase
