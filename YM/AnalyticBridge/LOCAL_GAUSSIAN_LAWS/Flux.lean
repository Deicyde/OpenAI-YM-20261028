import Mathlib.Analysis.Fourier.Convolution
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Accuracy
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.FREE_RESOLVENT.Flat
import YM.Push.FREE_RESOLVENT.JetWindows

/-!
# Native (one color) finite-period free curvature matrix from the actual horizon

P_j is first specified in
physical real counting forms.

Later identify its nonzero and zero
momentum values with the actual Free.Present train data.

`copper`
does NOT define a potential propagator at harmonic; only invert the
currents which will ever be tested (curl dual).

Choice independent.

This also applies with the nulls linked across moving trees on the
actual periods, maintaining exact periodic normalization.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Current
open Function Lattice Wilson RG Precision Exterior Tree Matrix
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side}
section Solve
variable {V W : Type} [Fintype V] [Fintype W] (q : Matrix W V ℝ) (M : Matrix W W ℝ) {a : ℝ}

def R := q.transpose*M*q

lemma right_of_count (h : Gap M a) (he : 0 < a) : ∃ Z : Matrix V W ℝ, R q M*Z=q.transpose := by
  let b := R q M
  have hi (u : V → ℝ) : b *ᵥ u = 0 ↔ q *ᵥ u=0 := by
    unfold b R
    rw [Matrix.mul_assoc,← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    constructor
    · intro H; have hh := congr_arg (dotProduct u) H
      change u ⬝ᵥ q.transpose *ᵥ _ = u ⬝ᵥ 0 at hh
      rw [dotProduct_mulVec,vecMul_transpose, dotProduct_zero] at hh
      have hx := h.lower (q *ᵥ u)
      rw [hh] at hx
      have hz : 0 ≤ (q *ᵥ u) ⬝ᵥ q *ᵥ u := by
        simpa only [star_trivial] using dotProduct_star_self_nonneg (q *ᵥ u)
      exact dotProduct_self_eq_zero.mp (by nlinarith)
    intro hu; rw [hu, Matrix.mulVec_zero,Matrix.mulVec_zero]
  have hk : b.mulVecLin.ker = q.mulVecLin.ker := by ext u; exact hi u
  have hd : b.rank=q.rank := by
    unfold Matrix.rank; have hh := b.mulVecLin.finrank_range_add_finrank_ker
    rw [hk] at hh; exact Nat.add_right_cancel (hh.trans q.mulVecLin.finrank_range_add_finrank_ker.symm)
  have hr : b.mulVecLin.range=q.transpose.mulVecLin.range := by
    apply Submodule.eq_of_le_of_finrank_le
    · rintro u (hh : _); obtain ⟨v,rfl⟩ := LinearMap.mem_range.mp hh
      refine LinearMap.mem_range.mpr ⟨(M*q) *ᵥ v,?_⟩; change q.transpose *ᵥ _=b *ᵥ v
      unfold b R; rw [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    change q.transpose.rank ≤ b.rank; rw [hd,Matrix.rank_transpose]
  have hv (k : W) : ∃ z : V → ℝ, b *ᵥ z=q.transpose *ᵥ Pi.single k 1 := by
    change q.transpose.mulVecLin (Pi.single k 1) ∈ b.mulVecLin.range
    rw [hr]; exact LinearMap.mem_range_self _ _
  choose z hz using hv
  let Z : Matrix V W ℝ := Matrix.of fun i a => z a i
  refine ⟨Z,?_⟩
  apply Matrix.ext_of_mulVec_single; intro k
  rw [← Matrix.mulVec_mulVec, ← hz]
  have he' : Z *ᵥ Pi.single k 1=z k := by ext i; simp [Matrix.mulVec,dotProduct,Z,Pi.single_apply,mul_ite]
  rw [he']

/-- Instance-free of prices; default not visible if floor inputs provided. -/
def holder : Matrix V W ℝ := if h : ∃ Z : Matrix V W ℝ, R q M * Z=q.transpose then h.choose else 0

lemma holder_value (h : Gap M a) (he : 0<a) : R q M*holder q M=q.transpose := by
  rw [holder,dif_pos (right_of_count q M h he)]; exact Exists.choose_spec (right_of_count q M h he)

def copper := q*holder q M



lemma flux_psd (h : Gap M a) (he : 0<a) (hv : M.transpose=M) : (copper q M).PosSemidef := by
  have hd := holder_value q M h he
  let z:=holder q M
  have ht : z.transpose*R q M=q := by
    unfold z
    have hh := congr_arg Matrix.transpose hd
    simpa only [R,transpose_mul,transpose_transpose, hv,Matrix.mul_assoc] using hh
  have hp : M.PosSemidef := (gap_positive (show M.IsSymm from hv) h he).posSemidef
  have hk : (R q M).PosSemidef := by
    unfold R
    convert hp.conjTranspose_mul_mul_same q
    all_goals simp
  have hh := hk.conjTranspose_mul_mul_same z
  change (q*z).PosSemidef
  rw [← ht]; simpa using hh

lemma flux_symm (h : Gap M a) (he : 0<a) (hv : M.transpose=M) : (copper q M).transpose=copper q M :=
  isHermitian_iff_isSymm.mp (flux_psd q M h he hv).isHermitian
end Solve

def learned (H : Bed) (n : Side) := copper (d 1 n) (H.metric.acts n)



-- color-tensor bookkeeping (counting)
section Book
variable {r s t : ℕ}
lemma tensor_mul (G : Gauge) (B : Matrix (Body r f) (Body s c) ℝ) (X : Matrix (Body s c) (Body t n) ℝ) :
    tensor G (B*X)=tensor G B*tensor G X := by
  apply Matrix.ext_of_mulVec_single; intro i
  rw [← Matrix.mulVec_mulVec]
  funext x; rcases x with ⟨x,a,j⟩
  change component (tensor G (B*X) *ᵥ Pi.single i 1) j (x,a)=component (tensor G B *ᵥ (tensor G X *ᵥ Pi.single i 1)) j (x,a)
  rw [component_mul,component_mul,component_mul,Matrix.mulVec_mulVec]
lemma tensor_add (G : Gauge) (B X : Matrix (Body r f) (Body s c) ℝ) : tensor G (B+X)=tensor G B+tensor G X := by
  ext i j; unfold tensor; simp; split <;> simp
lemma tensor_sub (G : Gauge) (B X : Matrix (Body r f) (Body s c) ℝ) : tensor G (B-X)=tensor G B-tensor G X := by
  ext i j; unfold tensor; simp; split <;> simp

lemma tensor_nil (G : Gauge) : tensor G (0:Matrix (Body r f) (Body s c) ℝ)=0 := by
  ext i j; simp [tensor]


end Book
end YM.AnalyticBridge.LocalGaussianLaws.Current
