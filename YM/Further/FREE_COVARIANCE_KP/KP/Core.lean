import YM.Further.FREE_COVARIANCE_KP.KP.Floor

/-! # Free potential precision compared on an enlarged real-frequency cell -/

set_option autoImplicit false
noncomputable section
namespace YM.Further.FreeCovariance.KP
open Filter Set Function Metric Complex Matrix Work.F06 Exterior Precision Bloch Lattice Laurent
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate
variable {α Ω η : ℝ}

abbrev X1 := TypeFace 1
abbrev X2 := TypeFace 2
def earth := 3*Real.pi/2
theorem earth_pos : 0<earth := by unfold earth; positivity

def premier : Set E4 := {p | ∀ i, |p i| < earth}
def search : Window := ⟨premier ∩ {0}ᶜ, by
    apply IsOpen.inter _ isOpen_compl_singleton
    rw [show premier = ⋂ i:Axis, {p:E4 | |p i| < earth} from by ext; simp [premier]]
    exact isOpen_iInter_of_finite fun i => isOpen_lt (by fun_prop) continuous_const,
    fun h => h.2 rfl⟩
lemma search_short (p:E4) (hp : p∈search) : ‖p‖ ≤ 2*earth := by
  apply le_of_sq_le_sq _ (by positivity [earth_pos]); rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _ : Axis,earth^2 := by
      apply Finset.sum_le_sum; intro i _; gcongr; exact (hp.1 i).le
    _ = _ := by simp; ring

/-- Coulomb extension by longitudinal block (cochain coordinates). -/
def outside (H : Matrix X2 X2 ℂ) (z : Axis → ℂ) :=
  (wedge 1 z)ᴴ * H * wedge 1 z + wedge 0 z * (wedge 0 z)ᴴ

def turned (p : E4) (i : Axis) := london (basis i) p
lemma turned_at (p i) : turned p i = I*(↑(p i):ℂ) := by rw [turned,london_at,basis_inner]
def tooth (p : E4) : Axis→ℂ := q (mcast p)
def spine (p : E4) : ℂ := ↑(‖p‖^2)
lemma turn_length (p:E4) : ↑(sqLength (turned p))=spine p := by
  unfold spine; rw [sqLength_apply,PiLp.norm_sq_eq_of_L2]; simp [turned_at]

lemma blade_id (z : Axis → ℂ) : outside 1 z = ((↑(sqLength z) : ℂ)) • 1 := by
  have hh (r : ℕ) (k : Axis) : (left ℂ r k)ᴴ=(left ℂ r k).transpose := by
    ext i j
    simp only [conjTranspose_apply, transpose_apply,Exterior.left,of_apply]
    split_ifs <;> simp [parity]
  have he (v : X1 → ℂ) : outside 1 z*ᵥv=(((sqLength z):ℂ) • (1:Matrix X1 X1 ℂ))*ᵥv := by
    have hv (r : ℕ) : (wedge r z)ᴴ=∑ i, star (z i) • (left ℂ r i).transpose := by unfold wedge; simp only [conjTranspose_sum,conjTranspose_smul,hh]
    rw [outside,Matrix.mul_one,Matrix.add_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,hv,hv]
    simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum, Matrix.mulVec_smul,← Finset.sum_add_distrib,Matrix.one_mulVec, ← smul_add]
    have hu (i : Axis) := cartan v z i
    simp_rw [add_comm ((left ℂ 1 _).transpose *ᵥ _),hu,smul_smul]
    rw [← Finset.sum_smul]; congr 1
    rw [sqLength_apply,ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  apply Matrix.toLin'.injective; ext v; exact congr_fun (he _) _

lemma london_exact (p : E4) : outside 1 (turned p) = spine p • 1 := by rw [blade_id,turn_length]
lemma q_exact (p i) : tooth p i = song (basis i) p-1 := by rw [song,london_at,basis_inner]; rfl

def fuel (f : Firm α Ω η) (p : E4) := outside (f.row.read (mcast p)) (tooth p)
def tank (f : Firm α Ω η) (p : E4) := (spine p)⁻¹ • fuel f p
lemma pull_change {A : Matrix X2 X1 ℂ} {H : Matrix X2 X2 ℂ} (x : X1 → ℂ) :
    pairingRe (Aᴴ*H*A) x x=pairingRe H (A *ᵥ x) (A *ᵥ x) := by
      unfold pairingRe
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec,dotProduct_mulVec,← Matrix.star_mulVec,← Matrix.mulVec_mulVec]
lemma ion (f : Firm α Ω η) (ha : 0<α) (p : E4) (x : X1 → ℂ) : min η 1 * sqLength (tooth p) * sqLength x ≤ pairingRe (fuel f p) x x := by
  let A := wedge 1 (tooth p); let B := (wedge 0 (tooth p))ᴴ
  have hu H : pairingRe (outside H (tooth p)) x x=pairingRe H (A*ᵥx) (A*ᵥx)+sqLength (B*ᵥx) := by
    rw [outside,pairingRe_add,pull_change]
    have he : Bᴴ=(wedge 0 (tooth p)) := conjTranspose_conjTranspose _; congr 1; rw [← pairingRe_gram,he]
  have he := hu 1
  rw [blade_id,pairingRe_scale] at he
  have hh (j : ℕ) (x : TypeFace j → ℂ) : pairingRe 1 x x=sqLength x := by simp [pairingRe,sqLength]
  rw [hh,hh] at he
  rw [fuel,hu,mul_assoc,he,mul_add]; apply add_le_add
  · exact (mul_le_mul_of_nonneg_right (min_le_left ..) (sqLength_nonneg _)).trans (real_price ha p _)
  exact mul_le_of_le_one_left (sqLength_nonneg _) (min_le_right ..)

private lemma chip_lower : ∃ b : ℝ, 0<b ∧ ∀ r : ℝ, |r| ≤ earth → b*|r| ≤ ‖exp (I*(r:ℂ))-1‖ := by
  let F (r:ℝ) := exp (I*(r:ℂ))
  have hd : HasDerivAt F I 0 := by simpa [F] using (((ofRealCLM.hasFDerivAt (x:=0)).hasDerivAt).const_mul I).cexp
  let D := dslope F 0
  have ht : Continuous D := by
    refine continuous_iff_continuousAt.mpr fun x => ?_; by_cases h : x=0
    · subst x; exact continuousAt_dslope_same.mpr hd.differentiableAt
    exact (continuousAt_dslope_of_ne h).mpr (by unfold F; fun_prop)
  let S := closedBall (0:ℝ) earth
  have hh (r : ℝ) : r • D r= F r-1 := by
    by_cases h : r=0
    · simp [h,F]
    rw [show D r=slope F 0 r from dslope_of_ne F h,slope_def_module,sub_zero,smul_inv_smul₀ h]; simp [F]
  have hf (r : ℝ) (hr : r∈S) : D r≠0 := by
    by_cases h : r=0
    · unfold D; rw [h, dslope_same, hd.deriv]; exact I_ne_zero
    intro he
    have hw := hh r; rw [he,smul_zero] at hw
    obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp (sub_eq_zero.mp hw.symm)
    have he := congr_arg Complex.im hk
    simp only [Complex.mul_im,Complex.intCast_re,Complex.intCast_im, Complex.re_ofNat, Complex.im_ofNat, 
      Complex.ofReal_re, Complex.ofReal_im, I_im,I_re, Complex.mul_re,mul_zero, zero_add,zero_mul, one_mul,mul_one,sub_zero,add_zero] at he
    have hπ := Real.pi_pos
    have hp : |r|≤3*Real.pi/2 := mem_closedBall_zero_iff.mp hr
    rcases lt_trichotomy k 0 with hc|hc|hc
    · have hb : (k:ℝ) ≤ -1 := by exact_mod_cast (show k ≤ (-1:ℤ) by omega)
      exact (abs_le.mp hp).1.not_gt (by nlinarith)
    · simp [hc] at he; exact h he
    have hb : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ)≤k by omega)
    exact (abs_le.mp hp).2.not_gt (by nlinarith)
  obtain ⟨r,hr,h⟩ := (isCompact_closedBall (0:ℝ) earth).exists_isMinOn ⟨0,mem_closedBall_self earth_pos.le⟩ ht.norm.continuousOn
  refine ⟨‖D r‖,norm_pos_iff.mpr (hf r hr),fun x hx => ?_⟩
  change _ ≤ ‖F x-1‖; rw [← hh,norm_smul,Real.norm_eq_abs,mul_comm]; gcongr; exact h (mem_closedBall_zero_iff.mpr hx)

theorem tank_full (ha : 0<α) (he : 0<η) (Ω : ℝ) : ∃ b : ℝ, 0<b ∧ ∀ f : Firm α Ω η, ∀ p:E4, p ∈ search → ∀ x, b*sqLength x≤pairingRe (tank f p) x x := by
  obtain ⟨b,hb,H⟩ := chip_lower
  let m : ℝ := min η 1; have hm : 0<m := lt_min he one_pos
  refine ⟨m*b^2,by positivity,fun f p hp x => ?_⟩
  have hr := norm_pos_iff.mpr (search.out hp)
  have hZ : b^2* ‖p‖^2 ≤ sqLength (tooth p) := by
    rw [PiLp.norm_sq_eq_of_L2,Finset.mul_sum,sqLength_apply]; refine Finset.sum_le_sum fun i _ => ?_
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (H _ (hp.1 i).le) _
  rw [tank,spine, ← Complex.ofReal_inv,pairingRe_scale,mul_comm ((‖p‖^2)⁻¹),← div_eq_mul_inv,le_div_iff₀ (pow_pos hr _)]
  apply le_trans ?_ (ion f ha p x)
  rw [mul_right_comm _ (sqLength x),mul_assoc m]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ hm.le) (sqLength_nonneg _)
end YM.Further.FreeCovariance.KP
