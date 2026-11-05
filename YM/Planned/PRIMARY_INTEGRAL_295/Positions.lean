import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Next.WARD_BIN.Degree
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

/-!
# The filtration of polynomial link directions (tools)

Use honest E4 position polynomials for the lift (initial vertex
convention).

No assertion that *wrapping* reads use these polynomials.

`rangeLt E a` is strict: contains degrees `k < a`.

Work on real colors, including
real/matrix-multilinear coefficient formulas at the group logarithm.

The
filtration is for ordinary polynomials with constant tests; it is not the
quotient by polynomials on a window or torus.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Place
open Function Filter ContinuousMultilinearMap Labels Source.Drops WardBin
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

section

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

def exactDegree (k : ℕ) : Submodule ℝ (E4 → E) :=
    LinearMap.range ({ toFun M := Tensor.diagonal M, map_add' := by intro _ _; rfl,
                       map_smul' := by intro _ _; rfl } : Tensor.T E4 E k →ₗ[ℝ] (E4 → E))

def rangeLt : ℕ → Submodule ℝ (E4 → E)
  | 0 => ⊥
  | n+1 => exactDegree E n ⊔ rangeLt n

lemma rangeLt_succ (n : ℕ) : rangeLt E (n+1) = exactDegree E n ⊔ rangeLt E n := by rw [rangeLt]
lemma grows : Monotone (rangeLt E) := monotone_nat_of_le_succ fun i => by rw [rangeLt_succ]; exact le_sup_right

end

variable {E F X : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n a b : ℕ}

lemma can_write {f : E4 → E} : f ∈ exactDegree E n ↔ ∃ A : Tensor.T E4 E n, f = Tensor.diagonal A := by
  unfold exactDegree
  simp [LinearMap.mem_range,eq_comm]

lemma pure_sym {f : E4 → E} (h : f ∈ exactDegree E n) :
    ∃ A : Tensor.T E4 E n, Tensor.Sym A ∧ f=Tensor.diagonal A := by
  obtain ⟨A,rfl⟩ := can_write.1 h; exact ⟨_, Tensor.symmetrize_sym A, funext fun _ => (Tensor.symmetrize_diagonal A _).symm⟩

lemma simple (T : Tensor.T E4 E n) : Tensor.diagonal T ∈ exactDegree E n := can_write.2 ⟨T,rfl⟩

lemma exact_of_smooth {f : E4 → E} (h : ContDiffAt ℝ n f 0) (hS : ∀ (x : E4) (t : ℝ), f (t • x) = t^n • f x) :
    f ∈ exactDegree E n := by
  refine can_write.2 ⟨Tensor.coeff f n 0,?_⟩; funext x; rw [← leading_tensor x f h, funext (hS x), lead_monomial, if_pos rfl]

lemma exact_constant (v : E) : (fun _ => v) ∈ exactDegree E 0 :=
    exact_of_smooth contDiffAt_const (fun _ _ => by simp)
lemma exact_linear (v : E4 →L[ℝ] E) : (fun x => v x) ∈ exactDegree E 1 :=
    exact_of_smooth (v.contDiff.contDiffAt) (fun _ _ => by simp)
lemma exact_id : (fun x : E4 => x) ∈ exactDegree E4 1 := exact_linear (ContinuousLinearMap.id ..)

lemma exact_smooth {f : E4 → E} (h : f ∈ exactDegree E n) (r : WithTop ℕ∞) : ContDiff ℝ r f := by
  obtain ⟨A,rfl⟩ := can_write.1 h; exact Tensor.diag_smooth ..
lemma exact_scale {f : E4 → E} (h : f ∈ exactDegree E n) (x : E4) (t : ℝ) : f (t • x) = t^n • f x := by
  obtain ⟨A,rfl⟩ := can_write.1 h; exact Tensor.homogeneous ..

lemma linear_pure (u : E →L[ℝ] F) {f : E4 → E} (h : f ∈ exactDegree E n) :
    (fun x => u (f x)) ∈ exactDegree F n :=
    exact_of_smooth ((u.contDiff.comp (exact_smooth h _)).contDiffAt) (fun x t => by rw [exact_scale h, map_smul])

lemma multi_pure (M : Tensor.T E F n) (f : Fin n → E4 → E) (p : Fin n → ℕ) (h : ∀ i, f i ∈ exactDegree E (p i)) :
    (fun x => M fun i => f i x) ∈ exactDegree F (∑ i, p i) := by
  apply exact_of_smooth ((M.contDiff.comp <| contDiff_pi.mpr fun i => exact_smooth (h i) _).contDiffAt :
    ContDiffAt ℝ (↑(∑ i, p i)) (fun x => M fun i => f i x) (0:E4))
  intro x t
  change M (fun i => f i (t • x)) = _
  simp_rw [fun i => exact_scale (h i) x t, M.map_smul_univ, Finset.prod_pow_eq_pow_sum]
  rfl

lemma exact_le_band (hn : n < a) : exactDegree E n ≤ rangeLt E a :=
    le_trans (rangeLt_succ E n |>.symm.le.trans' (le_sup_left)) (grows E hn)

lemma linear_band (u : E →L[ℝ] F) (n : ℕ) {f : E4 → E} (h : f ∈ rangeLt E n) :
    (fun x => u (f x)) ∈ rangeLt F n := by
  induction n generalizing f with
  | zero =>
    rw [rangeLt] at *; rw [Submodule.mem_bot] at h; rw [Submodule.mem_bot, h]; exact funext fun _ => map_zero u
  | succ n ih =>
    rw [rangeLt_succ] at h
    obtain ⟨p,hp,q,hq,rfl⟩ := Submodule.mem_sup.mp h
    rw [show (fun x => u ((p+q) x))=(fun x => u (p x))+(fun x => u (q x)) by ext; simp]
    exact Submodule.add_mem _ (exact_le_band (Nat.lt_succ_self _) (linear_pure u hp)) (grows F n.le_succ (ih hq))

lemma range_decompose {f : E4 → E} (h : f ∈ rangeLt E n) :
    ∃ P : Fin n → E4 → E, (∀ i, P i ∈ exactDegree E i.val) ∧ f=∑ i, P i := by
  classical
  induction n generalizing f with
  | zero =>
    rw [rangeLt, Submodule.mem_bot] at h; exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simpa using h⟩
  | succ n ih =>
    rw [rangeLt_succ] at h; obtain ⟨p,hp,q,hq,rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨P,hP,rfl⟩ := ih hq
    refine ⟨Fin.snoc P p,fun i => ?_,?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last]; exact hp
      rw [Fin.snoc_castSucc]; exact hP j
    rw [Fin.sum_univ_castSucc]; simp [add_comm]

lemma multi_band (M : Tensor.T E F n) (f : Fin n → E4 → E) (p : Fin n → ℕ)
    (h : ∀ i, f i ∈ rangeLt E (p i+1)) : (fun x => M fun i => f i x) ∈ rangeLt F ((∑ i, p i)+1) := by
  classical
  choose P hP hp using fun i => range_decompose (h i)
  let V := ∀ i, Fin (p i+1)
  let g (b : V) (x : E4) := M fun i => P i (b i) x
  have he : (fun x => M fun i => f i x)=∑ b, g b := by
    funext x; simp_rw [hp,Finset.sum_apply]; exact M.map_sum (fun i j => P i j x)
  rw [he]; apply Submodule.sum_mem; intro b _
  have hx (i : Fin n) : (b i).val ≤ p i := Nat.le_of_lt_succ (b i).isLt
  exact exact_le_band (Nat.lt_succ_of_le (Finset.sum_le_sum (fun i _ => hx i)))
    (multi_pure M _ _ (fun i => hP i _))

lemma combine {A : E4 → E} {B : E4 → F} (hA : A ∈ rangeLt E n) (hB : B ∈ rangeLt F n) :
    (fun x => (A x,B x)) ∈ rangeLt (E × F) n := by
  let L : E →L[ℝ] (E×F) := ContinuousLinearMap.inl ..
  let R : F →L[ℝ] (E×F) := ContinuousLinearMap.inr ..
  rw [show (fun x => (A x,B x))=(fun x => L (A x))+(fun x => R (B x)) from
    funext fun x => by simp [L,R]]
  exact Submodule.add_mem _ (linear_band _ _ hA) (linear_band _ _ hB)

variable {ι : Type*} {W : ι → Type*} [Fintype ι] [∀ i,NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

lemma vector_pure (v : ∀ i, E4 → W i) (h : ∀ i, v i ∈ exactDegree (W i) n) :
    (fun x i => v i x) ∈ exactDegree (∀ i, W i) n :=
    exact_of_smooth (contDiffAt_pi.mpr fun i => (exact_smooth (h i) _).contDiffAt)
      (fun x t => funext fun i => exact_scale (h i) x t)

lemma vector_band (v : ∀ i, E4 → W i) (h : ∀ i, v i ∈ rangeLt (W i) n) :
    (fun x i => v i x) ∈ rangeLt (∀ i, W i) n := by
  classical
  let u (i : ι) (x : E4) := Pi.single i (v i x)
  rw [show (fun x i => v i x) = ∑ i, u i from funext fun x => by rw [Finset.sum_apply]; exact (Finset.univ_sum_single _).symm]
  exact Submodule.sum_mem _ fun i _ => linear_band (ContinuousLinearMap.single ℝ W i) _ (h i)

lemma exact_growth {f : E4 → E} (h : f ∈ exactDegree E n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * ‖x‖^n := by
  classical
  obtain ⟨A,rfl⟩ := can_write.1 h
  exact ⟨‖A‖, norm_nonneg _, fun x => by simpa [Tensor.diagonal] using A.le_opNorm (fun _ => x)⟩

lemma band_growth {f : E4 → E} (h : f ∈ rangeLt E n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C * (1+‖x‖)^n := by
  classical
  obtain ⟨P,hP,rfl⟩ := range_decompose h; choose C hC H using fun i => exact_growth (hP i)
  refine ⟨∑ i, C i,Finset.sum_nonneg fun i _ => hC i,fun x => ?_⟩
  rw [Finset.sum_apply, Finset.sum_mul]; refine (norm_sum_le ..).trans (Finset.sum_le_sum fun i _ => (H i x).trans ?_)
  apply mul_le_mul_of_nonneg_left _ (hC _)
  exact (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) _).trans
    (pow_le_pow_right₀ (by simp) i.isLt.le)

end YM.Planned.PrimaryIntegral295.Place
