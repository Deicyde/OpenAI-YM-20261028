import Mathlib
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Books
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Builder
import YM.Next.MAXWELL.Kernel
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Branches
import YM.Progress.STATIONARY_SCENES.Frames
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Ward
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Schur
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.SectorNext.VACUUM_NORMALIZATION.Plaques
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.FREE_STRESS_CERTIFICATE.ShellForce
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle
import YM.UVNext.PRICED_KERNELS.Echo

/-!
# Pricing operators & entries in normalized `BudgetPoint.dirBound` currency

After delay t' ≤ 2 t, with derivatives through q and polynomial charges
on every slot.

Counting Schur-test for actual marginal ℓ² matrix norm,
not an entry of a full-system inverse.

When evaluating Lie derivatives
in a rotated *varying* channel one must still differentiate any changed
orientations in the group function; no tensor pullback invariance assumed.

These costs are not derivative claims on an indicator crossing or estimates
of the complete kernel factors (e.g. μ_0 velocities or log Haar ratios).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Next.SectorChange Set WardBin.Lies
  YM.Pressure FreeResolvent Affine TestD Window Mark Matrix  Lever Schur Wisps
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical RealInnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {H : Tube G S} {bp : BudgetPoint} {s Y t d γ K g x : ℝ} {M : ℕ → ℝ}
  {q n j : ℕ} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {V : Config G c} {o : Site c}
  {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] {a : ι → Site c} {F : Config G c → Matrix ι ι ℝ}

omit [DecidableEq ι] in
lemma Book.part (h : Book (native c) a a Prod.fst q d γ M F V) {e : α → ι} (he : Injective e) :
    Book (native c) (a ∘ e) (a ∘ e) Prod.fst q d γ M (limitTo F e) V := by
  refine ⟨(selectL e).contDiff.contDiffAt.comp _ h.smooth,h.nonneg,fun j z hj => ?_⟩
  erw [ordered, show limitTo F e=(selectL e) ∘ F from rfl,Push.Local.left_linear (selectL e) (List.ofFn (unitDir ∘ z)) h.smooth (List.length_ofFn.trans_le hj)]
  exact (h.bill j z hj).submatrix he he

omit [DecidableEq ι] in
lemma Book.zeroth (h : Book (native c) a a Prod.fst q d γ M F V) : Pours (F V) a a γ (M 0) := by
  let z : Pins G c 0 := Fin.elim0
  have he := h.bill 0 z (Nat.zero_le _)
  simp only [List.ofFn_zero,ordered,List.ofFn_zero,leftDerivs] at he
  refine ⟨h.nonneg 0 (Nat.zero_le q),he.reclaim.rows.bound,fun j => ?_⟩
  simp_rw [separation_comm _ (a j)]; exact he.reclaim.cols.bound j

def tender (G : Gauge) (j P : ℕ) (s t K : ℝ) := K * ((torusPay (PAC G 1) s * polynomial s P)^j * if j=0 then 1 else 2*t)
lemma tender_nn (P : ℕ) (hs : 0 < s) (ht : 0 ≤ t) (hk : 0 ≤ K) : 0 ≤ tender G j P s t K := by
  have hv := torusPay_nn (PAC G 1) s hs; have hp := poly_le P hs; unfold tender; split <;> positivity
lemma tender_le (he : bp.threshold ≤ 2*t) (hs : 0 < s) (hk : 0 ≤ K) :
    fieldFee s bp.power bp.threshold (torusPay (PAC G 1) s) j * K ≤ tender G j bp.power s t K := by
  unfold fieldFee tender; rw [mul_pow,mul_pow, mul_comm _ K]; apply mul_le_mul_of_nonneg_left _ hk
  rw [mul_left_comm, mul_comm (bp.threshold^j)]; apply mul_le_mul_of_nonneg_left
  · split
    next h => simp [h]
    next h => exact (pow_le_pow_of_le_one bp.threshold_pos.le bp.threshold_le (Nat.pos_of_ne_zero h)).trans ((pow_one _).le.trans he)
  exact mul_nonneg (pow_nonneg (torusPay_nn _ _ hs) _) (pow_nonneg ((poly_le _ hs).trans' zero_le_one) _)

variable (h : Book (native c) a a Prod.fst q d γ M F V) (l : List (Directions G c)) (hl : l.length ≤ q) (he : bp.threshold ≤ 2*t) (hd : 0 < d)
  (hb : ∀ B ∈ l, bp.dirBound o B)
include h hl he hd hb
omit [DecidableEq ι] in
lemma Book.cash : Bill (radial _ (native c) o bp.power) (native c) a a l γ (tender G l.length bp.power (d/2) t (M l.length)) (leftDerivs F l V) :=
  (h.fields l hl hb (half_pos hd) (by linarith) bp.threshold_pos.le (volume c (PAC G 1) (d/2) (half_pos hd))).mono le_rfl (tender_le he (half_pos hd) (h.nonneg _ hl))

omit [DecidableEq ι] in
theorem Book.entries : let J := tender G l.length bp.power (d/2) t (M l.length)
    (∀ i, ∑ j, rate γ (separation (a i) (a j)) * |leftDerivs (fun V => F V i j) l V| ≤ J*((hill (native c) o bp.power (a i))^l.length)) ∧
    (∀ j, ∑ i, rate γ (separation (a i) (a j)) * |leftDerivs (fun V => F V i j) l V| ≤ J*((hill (native c) o bp.power (a j))^l.length)) := by
  intro J
  have ht (i j : ι) : leftDerivs (fun V => F V i j) l V = (leftDerivs F l V) i j := Push.Local.left_linear (evaluate i j) l h.smooth hl
  have hh := h.cash l hl he hd hb
  constructor <;> intro i
  · have hi := hh.row.rows i; rw [payment,inv_mul_eq_div,div_le_iff₀ (pow_pos (hill_pos ..) _)] at hi
    simp_rw [ht]; exact hi
  have hi := hh.col.rows i; rw [payment,inv_mul_eq_div,div_le_iff₀ (pow_pos (hill_pos ..) _)] at hi
  simp_rw [ht, separation_comm _ (a i)]; exact hi

omit h hl he hd hb
abbrev euclid (F : Config G c → Matrix ι ι ℝ) (v : Config G c) := toEuclideanCLM (𝕜:=ℝ) (F v)
lemma euclid_left (l : List (Directions G c)) (h : WardBin.Lies.Germ q F V) (hl : l.length ≤ q) : leftDerivs (euclid F) l V = toEuclideanCLM (𝕜:=ℝ) (leftDerivs F l V) :=
  Push.Local.left_linear ((toEuclideanCLM (n:=ι) (𝕜:=ℝ)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv.toContinuousLinearMap) l h hl

lemma pours_op {F : Matrix ι ι ℝ} (h : Pours F a a γ K) (hg : 0 ≤ γ) : ‖toEuclideanCLM (𝕜:=ℝ) F‖ ≤ K := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le h.pos
  intro x y hx hy
  rw [RCLike.re_to_real,real_inner_comm, Matrix.inner_toEuclideanCLM]
  refine (le_abs_self _).trans ((Schur.estimate (h.weaker (t:=0) (e:=K) hg le_rfl) _ _).trans ?_)
  rw [sumSq,sumSq,← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq,hx,hy]; linarith

lemma op_gap {F : Matrix ι ι ℝ} (h : FreeResolvent.Gap F g) (hg : 0 < g) (hK : 0 < K) (ho : ‖toEuclideanCLM (𝕜:=ℝ) F‖ ≤ K) : FreeResolvent.Gap F⁻¹ (g/K^2) := by
  constructor; intro y
  let z := F⁻¹ *ᵥ y
  have he : F *ᵥ z = y := by rw [mulVec_mulVec, F.mul_nonsing_inv (h.unit_det hg), one_mulVec]
  have hz := (toEuclideanCLM (𝕜:=ℝ) F).le_opNorm (WithLp.toLp 2 z)
  rw [toEuclideanCLM_toLp,he] at hz
  have hi := ((h.lower z).trans_eq (by rw [he,dotProduct_comm]))
  apply le_trans _ hi
  rw [div_mul_eq_mul_div,div_le_iff₀ (by positivity)]
  rw [← sumSq_dot,← sumSq_dot,sumSq,sumSq, show z = _ from (WithLp.ofLp_toLp 2 z).symm]
  have ee := pow_le_pow_left₀ (norm_nonneg _) (hz.trans (mul_le_mul_of_nonneg_right ho (norm_nonneg _))) 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq] at ee
  refine (mul_le_mul_of_nonneg_left ee hg.le).trans_eq ?_; ring

include h hl he hd hb
/-- Both normalized direction tests on a placed marginal can be used
at one origin of a connected kernel call (of extent R). Euclidean operator
norm on the **true ordered derivative**, not a Frobenius size-times-volume
bound. -/
theorem Book.operator (hg : 0 ≤ γ) (R : ℕ) (hr : ∀ i, separation (a i) o ≤ R) : ‖leftDerivs (euclid F) l V‖ ≤
    tender G l.length bp.power (d/2) t (M l.length) * ((1+(R:ℝ))^bp.power)^l.length := by
  rw [euclid_left l h.smooth hl]; apply pours_op (a:=a) _ hg
  obtain ⟨h1,h2⟩ := h.entries l hl he hd hb
  have ht (i j : ι) : leftDerivs F l V i j = leftDerivs (fun V => F V i j) l V := (Push.Local.left_linear (evaluate i j) l h.smooth hl).symm
  have hh := tender_nn (G:=G) (j:=l.length) bp.power (half_pos hd) (t:=t) (by linarith [bp.threshold_pos]) (h.nonneg _ hl)
  have hp (i) : (hill (native c) o bp.power (a i))^l.length ≤ ((1+(R:ℝ))^bp.power)^l.length := by
    refine pow_le_pow_left₀ (hill_pos ..).le (pow_le_pow_left₀ (by have := (native c).nonneg (a i) o; positivity)
      (add_le_add_right (show (native c).d (a i) o ≤ (R:ℝ) from Nat.cast_le.mpr (hr i)) _) _) _
  refine ⟨mul_nonneg hh (by positivity),fun i => ?_,fun i => ?_⟩
  · simp_rw [ht]; exact (h1 i).trans (mul_le_mul_of_nonneg_left (hp i) hh)
  simp_rw [ht]; exact (h2 i).trans (mul_le_mul_of_nonneg_left (hp i) hh)
end YM.SelectedOrderedKernels
