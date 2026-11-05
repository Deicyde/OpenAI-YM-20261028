import YM.Pert.Fourier.Floor
import YM.Next.RANK.Radian.Reliquary
import YM.Next.RANK.Radian.Nodes
/-! Compact annular comparison of the direct symbol with the standard Maxwell transform.
Momentum coordinates K in inverse physical cycles for integration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Band
open YM.Next.Rank.Radian MeasureTheory Filter Lattice Topology Set Function Metric
open scoped ContDiff BigOperators RealInnerProductSpace ENNReal

abbrev turn := 2*Real.pi
def factor (s : ℝ) := turn/s
-- q here angular and rescaled = (2pi/s)*K.
def radial (_D : List Axis) (s : ℝ) (k : E4) := factor s • k
def amp (D : List Axis) (s : ℝ) : ℂ := (s:ℂ)^((D.length:ℤ)-2)
def carrier (D : List Axis) (s t b : ℝ) (z k : E4) := amp D s * wave z k * major b k * middle D t (radial D s k)
lemma factor_pos (s : ℝ) (hs : 0<s) : 0 < factor s := by unfold factor; positivity
lemma factor_norm (s : ℝ) (hs : 0<s) : ‖factor s‖ = turn/s := Real.norm_of_nonneg (factor_pos s hs).le
lemma radial_apply (D : List Axis) (s : ℝ) (k : E4) (i : Axis) : radial D s k i = factor s * k i := PiLp.smul_apply ..
lemma radial_norm (D : List Axis) (s : ℝ) (hs : 0<s) (k : E4) : ‖radial D s k‖ = turn/s * ‖k‖ := by rw [radial,norm_smul, factor_norm _ hs]
lemma amp_cost (D : List Axis) (s : ℝ) (hs : 0<s) : ‖amp D s‖ = s^(D.length) * s⁻¹^2 := by
  unfold amp; rw [norm_zpow,zpow_sub₀ (norm_ne_zero_iff.mpr (Complex.ofReal_ne_zero.mpr hs.ne'))]; norm_cast; rw [Real.norm_of_nonneg hs.le,div_eq_mul_inv,inv_pow]
lemma disk_alter (t : ℝ) (ht : 0<t) : ContDiff ℝ ∞ (fun q : E4 => disk ((factor t) • q)) := disk.contDiff.comp ((show ContDiff ℝ ∞ id from contDiff_id).const_smul _)
lemma major_cont : ContDiff ℝ ∞ (uncurry major) := Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp ((contDiff_fst (𝕜:=ℝ) (n:=∞)).neg.mul ((contDiff_norm_sq ℝ).comp contDiff_snd)))
lemma carrier_general (D : List Axis) (s : ℝ) (hs : s>0) {t : ℝ} (ht : |t|≤1) (b : ℝ) (z : E4) (x : E4) : ContinuousAt (carrier D s t b z) x := by
  have he := (middle_diff D t ht (radial D s x)).continuousAt.comp (f:=fun k : E4 => (t,radial D s k)) (show ContinuousAt (fun k : E4 => (t,radial D s k)) x from continuousAt_const.prodMk ((by unfold radial; fun_prop) : ContinuousAt (radial D s) x))
  exact ((continuousAt_const.mul (by unfold wave; fun_prop) : ContinuousAt (fun k=> amp D s * wave z k) x).mul (major_cont.continuous.continuousAt.comp (show ContinuousAt (fun k => (b,k)) x by fun_prop))).mul he

lemma major_le (b : ℝ) (hb : b≥0) (x : E4) : ‖major b x‖ ≤ 1 := by rw [major,Complex.norm_real, Real.norm_of_nonneg (by positivity)]; apply Real.exp_le_one_iff.mpr; exact mul_nonpos_of_nonpos_of_nonneg (by linarith only [hb]) (sq_nonneg _)
lemma together (D : List Axis) (s : ℝ) (hs : s>0) (R : ℕ) {t : ℝ} (ht : 0≤t) (h1 : t≤1) (b : ℝ) (z : E4) (x : E4) (hR : 2*s/turn ≤ R) (hx : ↑R < ‖x‖) : carrier D s t b z x = 0 := by
  have he : 0 < turn := by positivity
  have hr : 2 ≤ ‖radial D s x‖ := by rw [radial_norm D s hs, div_mul_eq_mul_div]; exact (le_div_iff₀ hs).mpr (by have hv := (div_le_iff₀ he).mp (hR.trans hx.le); linarith only [hv])
  simp only [carrier,middle,outermost hr, disk_out (one_le_two.trans hr),sub_zero]; simp
lemma compact_support (D : List Axis) (s : ℝ) (hs : s>0) (b z) {t : ℝ} (ht : 0≤t) (h1 : t≤1) : HasCompactSupport (carrier D s t b z) := by
  obtain ⟨R,hR⟩ : ∃ R : ℕ, 2*s/turn ≤ R := exists_nat_ge _
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0:E4) R) isClosed_closure (closure_minimal _ isClosed_closedBall)
  rintro x hx
  rw [mem_closedBall,dist_zero_right]; exact le_of_not_gt (fun h => hx (together D s hs _ ht h1 _ _ _ hR h))
lemma compact_int (D : List Axis) (s : ℝ) (hs : s>0) {t : ℝ} (ht : 0≤t) (h1 : t≤1) (b z) : Integrable (carrier D s t b z) volume :=
  Continuous.integrable_of_hasCompactSupport (continuous_iff_continuousAt.mpr (carrier_general _ _ hs (by rwa [abs_of_nonneg ht]) _ _)) (compact_support _ _ hs _ _ ht h1)
lemma wide_bound (D : List Axis) (s : ℝ) (hs : s>0) : ∃ C>0, ∀ {a b : ℝ}, 0≤a → a≤1 → 0≤b → ∀ z k, ‖carrier D s a b z k‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := middle_bound 0 D
  refine ⟨max 1 (‖amp D s‖ * C),lt_of_lt_of_le zero_lt_one (le_max_left ..),fun ht h1 hb z k=>le_trans ?_ (le_max_right ..)⟩
  rename_i a b; unfold carrier
  simp only [Complex.norm_mul]; simp only [YM.Next.Rank.Radian.wave,Circle.norm_coe,mul_one]
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (major_le _ hb _)) (norm_nonneg _)) (mul_le_mul_of_nonneg_left _ (norm_nonneg _))
  by_cases hk : ‖radial D s k‖≤3
  · simpa only [norm_iteratedFDeriv_zero] using h (a,radial D s k) ⟨ht,h1⟩ (mem_closedBall.mpr (by simp [show ‖radial D s k‖≤6 by linarith]))
  have hr := le_trans (show (2:ℝ) ≤ 3 by norm_num) (le_of_lt (not_le.mp hk)); simp only [middle, disk_out (one_le_two.trans hr), outermost hr]; simp [hC.le]

lemma major_glow (D : List Axis) (s b : ℝ) (hs : s>0) (k : E4) : major (b/(factor s)^2) (radial D s k) = major b k := by
  unfold major; rw [radial_norm D s hs]; congr 2; rw [factor]; field_simp
lemma baseD (D : List Axis) (s : ℝ) (hs : 0<s) (k : E4) : press D (liturgy 0) k = amp D s * symbol D 0 (radial D s k) := by
  have ht := factor_pos s hs; have hne : (s:ℂ) ≠0 := Complex.ofReal_ne_zero.mpr hs.ne'; have e : (s:ℂ)* ↑(factor s) = (turn:ℂ) := by unfold turn factor; push_cast; field_simp [hne]
  have hd (i : Axis) : (s:ℂ)*numerator 0 (radial D s k) i = chirp i k := by
    simp only [numerator,radial_apply, zero_mul, phaseQ_zero, chirp, Complex.ofReal_mul,turn]; push_cast at e
    grind
  have eq : ∀ L : List Axis, L.Sublist D ∨ True → press L (liturgy 0) k = (s:ℂ)^(L.length) * (L.map (numerator 0 (radial D s k))).prod * liturgy 0 k := by
    intro l; induction l with
    | nil => intro; simp [press]
    | cons i l ih => intro; change chirp i k * press _ _ k = _; rw [ih (.inr trivial),← hd, List.map_cons,List.prod_cons,List.length_cons,pow_succ];ring
  rw [eq D (.inr trivial)]
  have hdn : latticeD 0 (radial D s k) = (factor s)^2 * ‖k‖^2 := by simp [latticeD,radial_apply, Full.norm_four, sinQ_zero, Finset.mul_sum,mul_pow]
  unfold symbol amp liturgy; rw [hdn, major,show -(0:ℝ) * ‖k‖^2 = 0 from by ring,Real.exp_zero]
  unfold Maxwell.normal; rw [zpow_sub₀ (Complex.ofReal_ne_zero.mpr hs.ne'),zpow_natCast, show ((s:ℂ)^(2:ℤ))=(s:ℂ)^2 by norm_cast]; unfold factor turn; push_cast
  field_simp [hne] <;> ring
lemma base_glow (D : List Axis) (s b : ℝ) (hs : s>0) (k : E4) : press D (liturgy b) k = major b k * (amp D s * symbol D 0 (radial D s k)) := by
  rw [←baseD _ _ hs]
  induction D with
  | nil => unfold press liturgy; simp only [List.foldr_nil]; simp [major]; ring
  | cons i d ih => change _ * press d _ k = major b k * (_ * press d _ k); rw [ih]; ring
lemma untab (D : List Axis) (s b : ℝ) (hs : s>0) (k a : E4) : wave a k * press D (liturgy b) k = amp D s * wave a k * major b k * symbol D 0 (radial D s k) := by rw [base_glow _ _ _ hs];ring
end YM.Pert.Band
