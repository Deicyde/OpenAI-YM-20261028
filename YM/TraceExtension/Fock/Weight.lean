import YM.TraceExtension.Fock.Form

/-! Weighted square norm sectors. `env` weights independent of other
spacelike test functions. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {n d : ℕ}

abbrev Wave (n : ℕ) := Mom n →ₘ[photons n] ℂ
lemma wave_meas (q : Wave n) : Measurable (⇑q) := (AEEqFun.stronglyMeasurable _).measurable
def env (d : ℕ) (x : Space3) : ℝ := (1+‖x‖)^d
def shield (d : ℕ) (x : Mom n) : ℝ := ∏ i, env d (x i)
lemma env_positive (d x) : 0 < env d x := by unfold env; positivity
lemma env_one (d x) : 1 ≤ env d x := one_le_pow₀ (by simp)
lemma shield_pos (d) (x : Mom n) : 0 < shield d x := Finset.prod_pos fun _ _ => env_positive ..
lemma shield_one (d) (x : Mom n) : 1 ≤ shield d x := Finset.one_le_prod fun _ _ => env_one ..
@[fun_prop] lemma env_cont (d) : Continuous (env d) := by unfold env; fun_prop
@[fun_prop] lemma shield_cont (d) : Continuous (@shield n d) := by unfold shield; fun_prop
lemma shield_high (v : ℕ) (x : Mom n) : (1+‖x‖)^v ≤ shield v x := by
    cases n with
    | zero => rw [Subsingleton.elim x (0:Mom 0),norm_zero]; simp [shield]
    | succ n =>
      obtain ⟨i,hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (n+1))) (fun i => ‖x i‖) Finset.univ_nonempty
      have he : ‖x‖ ≤ ‖x i‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg (x i))).2 fun j=> hi.2 j (Finset.mem_univ _)
      apply le_trans (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1+‖x‖) (show 1+‖x‖≤1+‖x i‖ from by linarith) v); unfold shield; rw [← Finset.mul_prod_erase _ _ hi.1]; exact le_mul_of_one_le_right (env_positive v (x i)).le (Finset.one_le_prod fun k _ => env_one ..)

def tempered (q : Wave n) (d : ℕ) : Prop := MemLp (fun p => (↑(shield d p)⁻¹:ℂ) * q p) 2 (photons n)

lemma env_int : Integrable (fun x:Space3 => (env 2 x)⁻¹ ^2) photon := by
    have he := inverse_integrable (μ:=photon) (A:=Real.pi) (k:=2) Real.pi_pos.le (fun R hr => (photon_ball (zero_lt_one.trans_le hr)).le)
    apply he.mono' ((show Continuous _ from ((env_cont 2).inv₀ (fun x => (env_positive 2 x).ne')).pow 2).aestronglyMeasurable)
    filter_upwards with x
    change ‖(env 2 x)⁻¹^2‖ ≤ ((1+‖x‖)^3)⁻¹; rw [Real.norm_of_nonneg (sq_nonneg _), inv_pow]; apply inv_anti₀ (by positivity)
    unfold env; rw [← pow_mul]; exact pow_le_pow_right₀ (by simp) (by omega)
lemma shell_lp : MemLp (fun k : Mom n => (shield 2 k)⁻¹) 2 (photons n) := by
    apply (memLp_two_iff_integrable_sq ((shield_cont 2).inv₀ (fun i => (shield_pos _ i).ne')).aestronglyMeasurable).2
    convert Integrable.fintype_prod (fun i : Fin n=> env_int) using 1
    ext1 x
    unfold shield; rw [Pi.inv_apply,← Finset.prod_inv_distrib,Finset.prod_pow]
    rfl
lemma austere (f : Wave n) (h : tempered f d) :
    Integrable (fun k => ‖f k‖*(shield (d+2) k)⁻¹) (photons n) := by
    have hp : MemLp (fun k => ‖(↑(shield d k)⁻¹:ℂ)* f k‖) 2 (photons n) := h.norm
    apply Integrable.congr (shell_lp.integrable_mul hp)
    filter_upwards with k
    simp only [Pi.mul_apply,norm_mul]; change (shield 2 k)⁻¹ * (‖(_ : ℂ)‖ * ‖f k‖)=_
    have he : shield (d+2) k=shield d k *shield 2 k := by unfold shield env; simp_rw [pow_add,Finset.prod_mul_distrib]
    rw [he, mul_inv_rev]; simp [Real.norm_of_nonneg (shield_pos d k).le]; ring

variable {G : Gauge} {C : Family G} {a : Extraction.Order} {S : Table C.book}
    {F : Spec.Final C a S} {μ : Measure E4} {m : ℕ} {U : F.action.operators.H →ₗᵢ[ℂ] Ambient m}
    (Y : Form F U)

def Form.wave (i : Index m) : Wave i.1 := AEEqFun.mk (Y.val ∘ insertP i) (Y.leg.comp (embedP i).measurable).aestronglyMeasurable
lemma Form.val_wave (i : Index m) : ⇑(Y.wave i) =ᵐ[photons i.fst] Y.val ∘ insertP i := AEEqFun.coeFn_mk ..

def sectorsMass (q : Wave n) := (photons n).withDensity (fun p => ENNReal.ofReal (‖q p‖^2))
lemma sectors_eq (i : Index m) : sectorsMass (Y.wave i)=(photons i.fst).withDensity (Y.rent ∘ insertP i) := by
    unfold sectorsMass; apply withDensity_congr_ae; filter_upwards [Y.val_wave i] with p hp
    change _=Y.rent _; rw [hp]; unfold Form.rent; simp only [← ofReal_norm,ENNReal.ofReal_pow (norm_nonneg _)]; rfl
lemma pieces (X : Comparison F U) (h : TraceSpectrum F μ) {V : Set E4} (hv : MeasurableSet V) :
    μ V=∑' (i : Index m), sectorsMass (Y.wave i) {p | totalMomentum p∈V} := by
    rw [Y.recognize_terms X h hv]; congr! 1; ext1 i; rw [sectors_eq, withDensity_apply _ (s:={p|totalMomentum p∈V}) (total_cont.measurable hv)]
    rfl

def band (R : ℝ) : Set (Mom n) := {p | time (totalMomentum p) ≤ R}
lemma band_meas (R : ℝ) : MeasurableSet (band (n:=n) R) := (isClosed_le (Mink.clock_cont.comp total_cont) continuous_const).measurableSet
lemma ball_band (R : ℝ) : closedBall (0:Mom n) R ⊆ band ((n+1)*R) := fun x hx => by
    rw [mem_closedBall,dist_zero_right] at hx
    change time _≤_; rw [total_energy]; exact (Finset.sum_le_card_nsmul _ _ _ (fun i hi => (norm_le_pi_norm x i).trans hx)).trans (by
       simp; have he : 0 ≤ R := (norm_nonneg _).trans hx; linarith)

lemma parts (X : Comparison F U) (h : TraceSpectrum F μ) (R : ℝ) :
    μ {p | time p≤R}=∑' i : Index m, sectorsMass (Y.wave i) (band R) :=
    pieces _ X h (isClosed_le Mink.clock_cont continuous_const).measurableSet
lemma Form.surface (X : Comparison F U) (h : TraceSpectrum F μ) (i : Index m) :
    ∃ d, tempered (Y.wave i) d := by
    obtain ⟨A,k,hA,hk⟩ := h.slab
    let q := Y.wave i; let L := sectorsMass q; let n := i.fst; let b : ℝ:=n+1
    have hb : 1 ≤ b := by unfold b; simp
    have hx (R : ℝ) (hR : 1≤R) : L (closedBall (0:Mom n) R) ≤ ENNReal.ofReal ((A*b^k)*R^k) := by
      refine (measure_mono (ball_band R)).trans ((show sectorsMass (Y.wave i) (band (b*R)) ≤ ∑' i:Index m,sectorsMass (Y.wave i) (band (b*R)) from ENNReal.le_tsum _).trans ?_)
      rw [← parts Y X h (b*R), mul_assoc,← mul_pow]; exact hk (b*R) (one_le_mul_of_one_le_of_one_le hb hR)
    have hv := inverse_integrable (hA:=show 0 ≤ A*b^k by positivity) (k:=k) hx
    have hp := wave_meas q
    let d := k+1
    refine ⟨d,(memLp_norm_iff ((by fun_prop : Measurable fun j : Mom n=> (↑(shield d j)⁻¹:ℂ)).mul hp |>.aestronglyMeasurable)).1 ((memLp_two_iff_integrable_sq ?_).2 ?_)⟩
    · fun_prop (disch := aesop)
    have hu : Integrable (fun x : Mom n => ((1+‖x‖)^d)⁻¹ * (ENNReal.ofReal (‖q x‖^2)).toReal) (photons n) :=
      (integrable_withDensity_iff ((hp.norm.pow_const _).ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).1 hv
    apply hu.mono'
    · change AEStronglyMeasurable (fun j : Mom n => ‖(↑(shield d j)⁻¹:ℂ)*q j‖^2) _; fun_prop
    filter_upwards with j
    rw [ENNReal.toReal_ofReal (sq_nonneg _)]
    simp only [Real.norm_of_nonneg (sq_nonneg _),Pi.mul_apply,norm_mul, mul_pow]
    change (‖(↑(shield d j)⁻¹:ℂ)‖)^2*‖q j‖^2 ≤ _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh := inv_le_one_of_one_le₀ (shield_one d j); have hP := shield_pos d j
    simp [Real.norm_of_nonneg hP.le];
    apply inv_anti₀ (by positivity); exact (shield_high d j).trans (by rw [pow_two]; exact le_mul_of_one_le_right hP.le (shield_one d j))
end YM.TraceExtension.Photons
