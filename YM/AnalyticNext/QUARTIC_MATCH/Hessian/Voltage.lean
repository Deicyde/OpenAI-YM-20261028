import YM.AnalyticNext.QUARTIC_MATCH.Hessian.Counting
import YM.Next.FREE_KERNELS.Bank
import YM.Next.FREE_KERNELS.Signal
import YM.PREC.Derivative


/-!
# On first and higher aliases (real momenta, including p=0)

Elementary exterior estimates paid at H¹ costs. Retain normalization for
unnormalized frame Fourier synthesis in further files.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Hessian
open Filter Function Lattice Laurent Bloch Exterior Matrix Precision RG
open  YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators ComplexConjugate
variable {c f : Side} (S : StepData c f)

section mesh
variable (p : Momentum)

def volt (p : Momentum) : ℝ := ∑ i, ‖tripQ 1 p i‖^2

lemma wedge_at_scalar (x : Axis → ℂ) (i) : wedge 0 x (axisEquiv i) vac=x i := by
  simp_rw [wedge, Matrix.sum_apply, Matrix.smul_apply,coord_map, left, Matrix.of_apply]
  rw [Finset.sum_eq_single i]; swap
  · intro j _ h; simp [coord,h]
  · have he : (({i}:Finset Axis).filter fun j => j < i)=∅ := Finset.filter_eq_empty_iff.mpr fun j hj => by rw [Finset.mem_singleton.mp hj]; exact lt_irrefl _
    simp [coord,vac,Exterior.remove, Exterior.parity, Exterior.pre, he]
  simp
lemma vane : ∑ i, star ((tripQ 1 p) i) * tripQ 1 p i=(volt p:ℂ) := by
  rw [volt,Complex.ofReal_sum]; simp_rw [Complex.star_def,← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
lemma heat0 : (signal 1 0 p)ᴴ*signal 1 0 p=(volt p:ℂ) • 1 := by
  ext i j; rw [vac_only i,vac_only j,mul_apply, ← Equiv.sum_comp axisEquiv, Matrix.smul_apply, Matrix.one_apply_eq,smul_eq_mul,mul_one]
  simp only [signal,Matrix.conjTranspose_apply,wedge_at_scalar, vane]
lemma heat1 : (signal 1 1 p)ᴴ*signal 1 1 p=(volt p:ℂ) • 1-signal 1 0 p*(signal 1 0 p)ᴴ := by
  unfold signal; rw [wedge_adj,wedge_adj, crossed 0]; rw [show (∑ i,star (tripQ 1 p) i*tripQ 1 p i)=_ from vane p]
lemma thermal0 (x : TypeFace 0→ℂ) : ell2 (signal 1 0 p *ᵥ x)^2=volt p * ell2 x^2 := by
  apply Complex.ofReal_injective; rw [Complex.ofReal_mul,← complex_count,← complex_count,
    adjoint_area, mulVec_mulVec,heat0, Matrix.smul_mulVec,one_mulVec,dotProduct_smul]; rfl
lemma thermal1 (x : TypeFace 1→ℂ) : ell2 (signal 1 1 p *ᵥ x)^2+
    ell2 ((signal 1 0 p)ᴴ *ᵥ x)^2=volt p * ell2 x^2 := by
  apply Complex.ofReal_injective; rw [Complex.ofReal_mul,Complex.ofReal_add,← complex_count,← complex_count,
    ← complex_count,adjoint_area,adjoint_area,mulVec_mulVec,mulVec_mulVec,conjTranspose_conjTranspose,
    heat1, sub_mulVec, dotProduct_sub, sub_add_cancel, smul_mulVec, one_mulVec, dotProduct_smul]; rfl
end mesh
section bill
local notation "M" => S.patch.L
local notation "L" => (S.patch.L.val:ℝ)

def lateFee := meter.low*zone
def earlyFee := 2 * (meter.high*domainRadius)
def pass (j : ℕ) := (plankMin^4)^j

lemma late_pos : 0 < lateFee := mul_pos meter.low_pos zone_pos
lemma early_pos : 0 < earlyFee := mul_pos two_pos (mul_pos meter.high_pos domainRadius_pos)
lemma pass_pos (j : ℕ) : 0 < pass j := pow_pos (pow_pos plankMin_pos 4) _

variable (p : Site c)

lemma cold (l : Site M) (he : l ≠ 0) : (lateFee/L)^2 ≤ volt (aliasAt (mon p) l) := by
  let y := aliasAt (mon p) l
  have hp : mon p ∈ cube zone := mem_cube_real (base_subset_realCube zone_pos (mon_mem _ _)) zone_pos
  have ht : y ∈ cube zone := alias_in_cube zone_pos hp l S.patch.odd_side
  obtain ⟨a,ha⟩ := Function.ne_iff.mp (show lift l ≠ 0 from fun h => he (lift_inj (by rw [h,lift_origin])))
  apply le_trans _ (Finset.single_le_sum (f:=fun i => ‖tripQ 1 y i‖^2) (fun i _ => sq_nonneg _) (Finset.mem_univ a))
  apply pow_le_pow_left₀ (div_nonneg late_pos.le (side_pos M).le)
  have hh : zone * up l a ≤ L*‖y a‖ := scaled_alias_lower l hp a ha
  have hv : zone ≤ zone*up l a := le_mul_of_one_le_right zone_pos.le (up_ge ..)
  apply (div_le_iff₀ (side_pos M)).mpr
  unfold tripQ
  have ht' := meter.below _ (zone_in_disk y ht a)
  change lateFee ≤ ‖(↑(1 : ℕ):ℂ)*chip (y a)‖*L
  simp only [Nat.cast_one,one_mul]
  calc
    _ ≤ meter.low * (L*‖y a‖) := mul_le_mul_of_nonneg_left (hv.trans hh) meter.low_pos.le
    _ ≤ _ := by rw [mul_left_comm,mul_comm L]; exact mul_le_mul_of_nonneg_right ht' (side_pos M).le

local notation "a₀" => aliasAt (mon p) (0:Site M)
lemma within (i : Axis) : L*‖a₀ i‖ ≤ domainRadius := by
  rw [alias_zero_eq,narrow_apply,norm_div,Complex.norm_natCast,mul_div_cancel₀ _ (side_pos M).ne']
  exact zone_in_disk _ (mem_cube_real (base_subset_realCube zone_pos (mon_mem _ _)) zone_pos) i
lemma mild (i : Axis) : plankMin ≤ ‖plank M (a₀ i)‖ :=
    plank_lower M _ (within S p i) ((physical_iff ..).mp (alias_real (real_frequency p) _) i)
lemma chilly : volt a₀ ≤ (earlyFee/L)^2 := by
  let C := meter.high*domainRadius
  have hh (i : Axis) : ‖tripQ 1 a₀ i‖ ≤ C/L := by
    apply (le_div_iff₀ (side_pos M)).mpr
    have h1 := within S p i
    have h2 := meter.above _ (narrow_norm _ h1)
    simp only [tripQ]
    change ‖(↑(1 : ℕ):ℂ)*chip _‖*_ ≤ _; simp only [Nat.cast_one,one_mul]
    exact (mul_le_mul_of_nonneg_right h2 (side_pos M).le).trans
      ((show _ = meter.high*(L*‖a₀ i‖) from by ring).trans_le (mul_le_mul_of_nonneg_left h1 meter.high_pos.le))
  have he := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => pow_le_pow_left₀ (norm_nonneg _) (hh i) 2
  apply he.trans_eq
  rw [Finset.sum_const, Finset.card_univ]
  unfold Axis earlyFee C; simp; ring
lemma credit : pass S.patch.J ≤ ‖massFilter S.patch a₀‖ := by
  unfold massFilter; rw [norm_pow]; apply pow_le_pow_left₀ (pow_nonneg plankMin_pos.le _) _
  unfold area; rw [norm_prod]
  apply le_trans _ (Finset.prod_le_prod (fun i (_ : i∈Finset.univ) => plankMin_pos.le) (fun i _ => mild S p i))
  simp [Axis]
lemma credit_start (i : Axis) : pass S.patch.J*plankMin ≤ ‖pullLine S.patch i a₀‖ := by
  unfold pullLine; rw [norm_mul]; exact mul_le_mul (credit S p) (rail_lower _ _ (within S p i)) plankMin_pos.le (norm_nonneg _)
end bill
end YM.AnalyticNext.QuarticMatch.Hessian
