import YM.Shoot.Criteria
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Laurent widths, signs

Native exponents and units.

Fourier on the lattice uses radian momenta;
conjugate symbol is continued from real torus (analytic star).

Coefficient matrices may use this entrywise over any finite axes, but check
whether constants must be pre-L when types themselves scale.

Absolute polynomial
losses of inverse width only after shrinking; keep weights explicit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Laurent
open Lattice Matrix Finset Filter
open RG
open scoped Topology BigOperators ContDiff

/-- multipatch multi indices. Not summed along any finite period. -/
abbrev Phase (α : Type*) := α → ℂ
abbrev Shift (α : Type*) := α → ℤ
abbrev On (α A : Type*) := Shift α → A

variable {α : Type*} {X : Type*}
variable [Fintype α]

/-- Unscaled one-norm -/
def size (x : Shift α) := ∑ i,(x i).natAbs
lemma size_add (x y : Shift α) : size (x+y) ≤ size x+size y := by
  unfold size; rw [← Finset.sum_add_distrib]; exact Finset.sum_le_sum fun i _ => Int.natAbs_add_le ..
lemma size_neg (x : Shift α) : size (-x)=size x := by simp [size]

def mode (p : Phase α) (x : Shift α) := Complex.exp (Complex.I*∑ i, p i*x i)

def Within (η : ℝ) (p : Phase α) := ∀ i, |(p i).im| ≤ η

def strip (η : ℝ) : Set (Phase α) := {p | ∀ i, |(p i).im|<η}
def cube (η : ℝ) : Set (Phase α) := strip η ∩ {p | ∀ i, |(p i).re|<Real.pi+η}

def reciprocal (x : Shift α) : Phase α := fun i => 2*(Real.pi:ℂ)*(x i)

lemma reward (p : Phase α) (x : Shift α) (η : ℝ) (hp : Within η p) : ‖mode p x‖ ≤ Real.exp (η*size x) := by
  unfold mode; rw [Complex.norm_exp]
  apply Real.exp_monotone
  simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub,Complex.im_sum,← Finset.sum_neg_distrib]
  simp only [Complex.mul_im,Complex.intCast_im,mul_zero,zero_add,Complex.intCast_re,size,Nat.cast_sum,Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (neg_le_abs (a := (p i).im*(x i))).trans ?_
  rw [abs_mul]; apply mul_le_mul_of_nonneg_right (hp i) (abs_nonneg _) |>.trans
  rw [← Int.cast_abs]; simp

@[simp] lemma mode_shift (p : Phase α) (x y : Shift α) : mode p (x+y)=mode p x*mode p y := by
  unfold mode; simp only [Pi.add_apply,Int.cast_add,mul_add, Finset.sum_add_distrib,Complex.exp_add]
@[simp] lemma mode_phase (p q : Phase α) (x : Shift α) : mode (p+q) x=mode p x*mode q x := by
  unfold mode; simp only [Pi.add_apply,add_mul, Finset.sum_add_distrib,mul_add,Complex.exp_add]
@[simp] lemma mode_zero (p : Phase α) : mode p 0=1 := by simp [mode]
@[simp] lemma mode_constant (x : Shift α) : mode 0 x=1 := by simp [mode]
@[simp] lemma mode_opposite (p : Phase α) (x : Shift α) : mode p (-x)=(mode p x)⁻¹ := by
  unfold mode; simp only [Pi.neg_apply, Int.cast_neg, mul_neg, Finset.sum_neg_distrib, Complex.exp_neg]
@[simp] lemma mode_inverse (p : Phase α) (x : Shift α) : mode (-p) x=(mode p x)⁻¹ := by
  unfold mode; simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, mul_neg, Complex.exp_neg]
@[simp] lemma mode_ne (p : Phase α) (x : Shift α) : mode p x≠0 := Complex.exp_ne_zero _

lemma mode_adjoint (p : Phase α) (x : Shift α) : star (mode (star p) x)=mode p (-x) := by
  unfold mode
  simp only [Pi.neg_apply, Int.cast_neg, Pi.star_apply, Complex.star_def, ← Complex.exp_conj]
  simp only [map_mul, Complex.conj_I,map_sum, starRingEnd_self_apply, map_intCast, mul_neg,
    Finset.sum_neg_distrib, neg_mul]

@[simp] lemma mode_periodic (x y : Shift α) : mode (reciprocal x) y=1 := by
  have e : Complex.I * (∑ i, reciprocal x i * y i) = (∑ i,x i * y i : ℤ) * (2*Real.pi*Complex.I) := by
    simp only [reciprocal, Finset.mul_sum, Int.cast_sum,Int.cast_mul,Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [mode,e,Complex.exp_int_mul_two_pi_mul_I]

lemma mode_scale (k : ℕ) (p : Phase α) (x : Shift α) : mode (k • p) x=mode p (k • x) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [add_smul,one_smul,mode_shift,mode_phase,ih]

lemma mode_real (p : Phase α) (x : Shift α) (hp : star p=p) : ‖mode p x‖=1 := by
  have he := mode_adjoint p x; rw [hp, mode_opposite] at he
  have hh := congr_arg (fun x : ℂ => ‖x‖) he
  rw [norm_star, norm_inv] at hh
  have hn : 0<‖mode p x‖ := norm_pos_iff.mpr (Complex.exp_ne_zero _)
  calc
    ‖mode p x‖ = 1 := by
      have hm : ‖mode p x‖*‖mode p x‖=1 := calc
        _ = ‖mode p x‖*‖mode p x‖⁻¹ := congr_arg (‖mode p x‖*·) hh
        _ = _ := mul_inv_cancel₀ hn.ne'
      nlinarith

section
variable [NormedAddCommGroup X]

/-- entry normalization uses X chosen by client. Absolute norm including sums
quantified (possibly infinite); actual finite Laurent degrees via `FiniteDegree`). -/
def Width (η A : ℝ) (f : On α X) := SumBudget (fun z => Real.exp (η*size z)*‖f z‖) A

def FiniteDegree (R : ℕ) (f : On α X) := ∀ z, R<size z → f z=0

lemma Width.mono {η η' A A' : ℝ} {f : On α X} (hf : Width η A f) (he : η'≤η) (ha : A≤A') : Width η' A' f := by
  have hb (z) : Real.exp (η'*size z)*‖f z‖≤Real.exp (η*size z)*‖f z‖ := mul_le_mul_of_nonneg_right
    (Real.exp_monotone (mul_le_mul_of_nonneg_right he (by positivity))) (norm_nonneg _)
  have hn (z) : 0 ≤ Real.exp (η'*size z)*‖f z‖ := by positivity
  have hs := hf.2.1.of_nonneg_of_le hn hb
  exact ⟨hn,hs, (hs.tsum_le_tsum hb hf.2.1).trans (hf.2.2.trans ha)⟩

lemma Width.unweighted {η A} {f : On α X} (h : Width η A f) (he : 0 ≤ η) : RG.SumBudget (fun i => ‖f i‖) A := by
  simpa only [Width,zero_mul,Real.exp_zero,one_mul] using h.mono he le_rfl

lemma Width.summable [CompleteSpace X] {η A} {f : On α X} (h : Width η A f) (he : 0 ≤ η) : Summable f :=
  ((h.unweighted he).2.1).of_norm

variable [NormedSpace ℂ X]

def read (f : On α X) (p : Phase α) := ∑' i, mode p i • f i

lemma Width.series {η A} {f : On α X} (h : Width η A f) (p : Phase α) (hp : Within η p) : SumBudget (fun i => ‖mode p i • f i‖) A := by
  have he (i) : ‖mode p i • f i‖ ≤ Real.exp (η*size i)*‖f i‖ := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_right (reward p i η hp) (norm_nonneg _)
  have hs := h.2.1.of_nonneg_of_le (fun i => norm_nonneg _) he
  exact ⟨fun _ => norm_nonneg _,hs,(hs.tsum_le_tsum he h.2.1).trans h.2.2⟩

lemma Width.estimate {η A} {f : On α X} (h : Width η A f) (p : Phase α) (hp : Within η p) : ‖read f p‖ ≤ A := by
  have he := h.series p hp
  exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2

lemma periodic (f : On α X) (p : Phase α) (x : Shift α) : read f (p+reciprocal x)=read f p := by simp only [read,mode_phase,mode_periodic,mul_one]
end
end YM.Laurent
