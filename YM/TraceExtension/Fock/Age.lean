import YM.TraceExtension.Fock.Branches

/-! Preserve high-energy growth bounds during spectral splitting. Work directly
with positive measures so no moment has been assigned finite mass implicitly. -/
set_option autoImplicit false
noncomputable section
namespace YM.TraceExtension.Photons
open Function Set Filter MeasureTheory Measure Metric Complex Mink Boundary Spectral
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace Classical
variable {n : ℕ}

def parcel (d : Fin n→ℝ) := {k : Mom n | ∀ i, ‖k i‖≤d i}
def barrel (n : ℕ) (k : ℕ) := parcel (n:=n) fun _=>2^k
lemma parcel_closed (d : Fin n→ℝ) : IsClosed (parcel d) := by
    rw [show parcel d = ⋂ i : Fin n, {k : Mom n | ‖k i‖≤d i} by ext; simp [parcel]]
    exact isClosed_iInter fun _=> isClosed_le (by fun_prop) continuous_const
lemma parcel_mono {a b : Fin n→ℝ} (h : a ≤ b) : parcel a ⊆ parcel b := fun _ hv i=> (hv i).trans (h _)
lemma barrel_mono {i j : ℕ} (h : i ≤ j) : barrel n i ⊆ barrel n j := parcel_mono (fun _=> pow_le_pow_right₀ (by norm_num) h)
lemma barrel_union : ⋃ i, barrel n i=univ := by
    refine eq_univ_of_forall fun x=> ?_
    obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt ‖x‖ (show 1<(2:ℝ) by norm_num)
    exact mem_iUnion.mpr ⟨k, fun i=> (norm_le_pi_norm _ _).trans hk.le⟩
lemma doubling_exact (d : Fin n→ℝ) (i) : doubling i ⁻¹' parcel (update d i (2*d i)) = parcel d := by
    have hh j k : ‖doubling i k j‖ ≤ update d i (2*d i) j ↔ ‖k j‖ ≤ d j := by
        by_cases h:j=i
        · subst j; simp [doubling,blow,norm_smul]
        simp [doubling,h,update_of_ne]
    ext x; exact forall_congr' fun j=> hh j x

lemma sectors_zero : sectorsMass (0:Wave n) = 0 := by
    unfold sectorsMass; rw [← withDensity_zero (μ:=photons n)]; apply withDensity_congr_ae
    filter_upwards [AEEqFun.coeFn_zero (μ:=photons n) (β:=ℂ)] with i hi; simp [hi]
lemma sectors_smul (q : Wave n) (c : ℝ) : sectorsMass (c • q)= ENNReal.ofReal (c^2) • sectorsMass q := by
    let W (x) := ENNReal.ofReal (‖q x‖^2)
    have he : Measurable W := ((wave_meas q).norm.pow_const _).ennreal_ofReal
    unfold sectorsMass; rw [← withDensity_smul _ he]; apply withDensity_congr_ae
    filter_upwards [AEEqFun.coeFn_smul c q] with x hx
    simp only [hx,Pi.smul_apply,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]; unfold W; rw [ENNReal.ofReal_mul (sq_nonneg c)]; rfl
lemma sectors_add (q r : Wave n) : sectorsMass (q+r) ≤ (2:ℝ≥0∞) • (sectorsMass q+sectorsMass r) := by
    let A (q : Wave n) (x) := ENNReal.ofReal (‖q x‖^2); have h q : Measurable (A q) := ((wave_meas q).norm.pow_const _).ennreal_ofReal
    unfold sectorsMass; rw [← withDensity_add_left (h q) (A r),← withDensity_smul _ ((h q).add (h r))]; apply withDensity_mono
    filter_upwards [AEEqFun.coeFn_add q r] with x hx; change _≤(2:ℝ≥0∞)*(A q x+A r x)
    unfold A; rw [hx,Pi.add_apply, ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    conv_rhs => lhs; rw [show (2:ℝ≥0∞) = ENNReal.ofReal 2 by norm_num]
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal; refine (sq_le_sq₀ (norm_nonneg (q x+r x)) (by positivity)).mpr (norm_add_le ..) |>.trans ?_ ; nlinarith [sq_nonneg (‖q x‖-‖r x‖)]
lemma sector_zoom (q : Wave n) (i : Fin n) :
    (sectorsMass (zoom i q)).map (doubling i)=(2⁻¹ ^2:ℝ≥0∞) • sectorsMass q := by
    ext A ha; unfold sectorsMass
    let z := fun p : Mom n => ENNReal.ofReal (‖q p‖^2); have he : Measurable z := ((wave_meas _).norm.pow_const _).ennreal_ofReal
    rw [Measure.map_apply (stretch i).measurable ha,withDensity_apply _ ((stretch i).measurable ha),← withDensity_smul_measure, ← (stretch i).map_eq,
       withDensity_apply _ ha,setLIntegral_map ha he (stretch i).measurable];
    apply lintegral_congr_ae
    filter_upwards [(zoom_ae i q).filter_mono (ae_restrict_le)] with x hx; simp only [hx]; rfl
lemma parcel_zoom (q : Wave n) (d : Fin n →ℝ) (i) : sectorsMass (zoom i q) (parcel d)=(2⁻¹^2:ℝ≥0∞)*sectorsMass q (parcel (update d i (2*d i))) := by
    rw [← doubling_exact d i, ← (dble_embed i).map_apply,sector_zoom]; rfl
lemma died {q : Wave n} (h : ∀ i, sectorsMass q (barrel n i)=0) : q=0 := by
    have he : ∫⁻ x, ENNReal.ofReal (‖q x‖^2) ∂photons n=0 := by
        have hp : sectorsMass q univ=0 := by rw [← barrel_union]; exact measure_iUnion_null h
        simpa [sectorsMass, withDensity_apply] using hp
    have ht := (lintegral_eq_zero_iff (((wave_meas q).norm.pow_const _).ennreal_ofReal)).1 he
    apply AEEqFun.ext; filter_upwards [ht,AEEqFun.coeFn_zero (μ:=photons n) (β:=ℂ)] with i hi hp; rw [hp]; simpa using hi

/-- Growth gate that roots of all sub-sector waves must preserve. -/
structure Evaporates (q : Wave n) : Prop where
    cover (i : ℕ) : sectorsMass q (barrel n i) < ⊤
    top : Tendsto (fun i => ENNReal.ofReal ((2^i:ℝ)⁻¹ ^ 8)*sectorsMass q (barrel n i)) atTop (𝓝 0)

def Margin (n : ℕ) : Submodule ℝ (Wave n) where
    carrier := {q|Evaporates q}
    zero_mem' := ⟨fun i=> by rw [sectors_zero]; simp, by simp_rw [sectors_zero]; simp⟩
    add_mem' := fun {x y} hx hy => by
        change Evaporates x at hx; change Evaporates y at hy; constructor
        · intro i; exact (sectors_add x y _).trans_lt (by rw [Measure.smul_apply, Measure.add_apply]; have hx:=hx.cover i; have hy:=hy.cover i; change 2* (_+_) < (⊤:ℝ≥0∞); finiteness)
        · let c (i : ℕ) := ENNReal.ofReal ((2^i:ℝ)⁻¹^8)
          have ht := ENNReal.Tendsto.const_mul (a:=2) (hx.top.add hy.top) (Or.inr (by norm_num))
          rw [add_zero,mul_zero] at ht; refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun i=> zero_le) fun i=>?_
          refine (mul_le_mul_right (sectors_add x y _) _).trans_eq ?_; rw [Measure.smul_apply,Measure.add_apply]
          rw [smul_eq_mul]; ring
    smul_mem' := fun c x hx => by
        change Evaporates x at hx; constructor
        · intro i; rw [sectors_smul,Measure.smul_apply]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hx.cover i)
        · simp_rw [sectors_smul,Measure.smul_apply, smul_eq_mul,mul_left_comm _ (ENNReal.ofReal (c^2))];
          convert ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal (c^2)) hx.top (Or.inr ENNReal.ofReal_ne_top) using 2; rw [mul_zero]
lemma zoom_margin (q : Wave n) (h : Evaporates q) (i : Fin n) : Evaporates (zoom i q) := by
    let f (k:ℕ) := fun _ : Fin n => (2:ℝ)^k
    have hm (k) : sectorsMass (zoom i q) (barrel n k) ≤ (2:ℝ≥0∞)⁻¹^2 * sectorsMass q (barrel n (1+k)) := by
        rw [barrel, parcel_zoom]; apply mul_le_mul_right (measure_mono (parcel_mono ?_)); intro j; by_cases h:j=i
        · subst j; rw [update_self]; simp [pow_add]
        exact (update_of_ne h ..).le.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_left k 1))
    constructor
    · intro k; exact (hm k).trans_lt (ENNReal.mul_lt_top (by finiteness) (h.cover _))
    have ht := h.top.comp (strictMono_nat_of_lt_succ (f:=fun k:ℕ=>1+k) (fun k=> Nat.add_lt_add_left (lt_add_one k) _) |>.tendsto_atTop)
    have hu := ENNReal.Tendsto.const_mul (a:=ENNReal.ofReal (2^6:ℝ)) ht (Or.inr ENNReal.ofReal_ne_top); rw [mul_zero] at hu
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu (fun _=>zero_le) fun k=> ?_
    refine (mul_le_mul_right (hm k) _).trans_eq ?_
    dsimp only [comp_apply]; rw [← mul_assoc, ← mul_assoc]; congr 1
    rw [← ENNReal.inv_pow,show (2:ℝ≥0∞)^2= ENNReal.ofReal ((2:ℝ)^2) by norm_num,
       ← ENNReal.ofReal_inv_of_pos (by positivity),← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1; rw [pow_add, pow_one]; field_simp
end YM.TraceExtension.Photons
