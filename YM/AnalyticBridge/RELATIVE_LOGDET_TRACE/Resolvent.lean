import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import YM.Push.FREE_RESOLVENT.Inverse





/-!
# Exact positive-sector log kernel, in physical counting coordinates

Everything here is real. Integrals are
Lebesgue (absolute integrability, including at zero). The subtraction is
**inside** the integral. In applications to different active spaces, take
the matrix on a single counting key type after reindexing BOTH matrices
and padding inactive keys by *ones* (see the sector interface). No requirement
that there are any keys at all.
-/
set_option autoImplicit false

noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet
open Filter Function Matrix Unitary MeasureTheory Set FreeResolvent
open scoped Topology BigOperators

/-- Shift decay. -/
def attenuation (u : ℝ) := (1+u)⁻¹

lemma attenuation_pos {u : ℝ} (hu : 0 ≤ u) : 0 < attenuation u := by unfold attenuation; positivity
lemma attenuation_le {u : ℝ} (hu : 0 ≤ u) : attenuation u ≤ 1 :=
  inv_le_one_of_one_le₀ (le_add_of_nonneg_right hu)

private lemma sink (a : ℝ) : Tendsto (fun u : ℝ => (a+u)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ _ tendsto_id)

lemma attenuation_square : IntegrableOn (fun u => attenuation u ^ 2) (Ioi 0) ∧
    (∫ u in Ioi 0, attenuation u ^ 2) = 1 := by
  let F := fun u => -attenuation u
  have ht : Tendsto F atTop (𝓝 0) := by simpa only [F,attenuation,neg_zero] using (sink 1).neg
  have he (u : ℝ) (h : u ∈ Ici 0) : HasDerivAt F (attenuation u ^ 2) u := by
    have hu := mem_Ici.mp h
    have hx := ((hasDerivAt_id' u).const_add 1).inv (show 1+u ≠ 0 from ne_of_gt (by linarith))
    simpa only [F,attenuation,one_div, neg_div,neg_neg,inv_pow] using! hx.neg
  have hi := integrableOn_Ioi_deriv_of_nonneg' he (fun _ _ => sq_nonneg _) ht
  exact ⟨hi, (integral_Ioi_of_hasDerivAt_of_tendsto' he hi ht).trans (by simp [F,attenuation])⟩

/-- Scalar real-spectral logarithm formula used **per entry**. -/
lemma log_scalar {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u => attenuation u - (a+u)⁻¹) (Ioi 0) ∧
      (∫ u in Ioi 0, attenuation u - (a+u)⁻¹) = Real.log a := by
  let F := fun u => Real.log (1+u) - Real.log (a+u)
  have ht : Tendsto F atTop (𝓝 0) := by
    have he : Tendsto (fun u : ℝ => (1+u)/(a+u)) atTop (𝓝 1) := by
      have hi : Tendsto (fun u : ℝ => 1 + (1-a)*(a+u)⁻¹) atTop (𝓝 1) := by
        simpa using! (((sink a).const_mul (1-a)).const_add 1)
      refine hi.congr' ?_
      filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
      field_simp
      ring
    have hm := he.log (by norm_num)
    rw [Real.log_one] at hm
    apply hm.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with x hx
    exact Real.log_div (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
  have hd (u : ℝ) (hu : u ∈ Ici 0) : HasDerivAt F (attenuation u - (a+u)⁻¹) u := by
    have hx := mem_Ici.mp hu
    have h (x : ℝ) (hp : 0<x) := ((hasDerivAt_id' u).const_add x).log (show x+u ≠ 0 from ne_of_gt (by linarith))
    simpa only [F,attenuation, one_div] using! (h 1 zero_lt_one).sub (h a ha)
  suffices h : IntegrableOn (fun u => attenuation u - (a+u)⁻¹) (Ioi 0) from
    ⟨h, by simpa only [F,add_zero,Real.log_one,zero_sub,neg_neg] using integral_Ioi_of_hasDerivAt_of_tendsto' hd h ht⟩
  rcases le_total 1 a with h|h
  · exact integrableOn_Ioi_deriv_of_nonneg' hd (fun x hx => sub_nonneg.mpr
      (inv_anti₀ (by have := mem_Ioi.mp hx; positivity) (by linarith))) ht
  exact integrableOn_Ioi_deriv_of_nonpos' hd (fun x hx => sub_nonpos.mpr
    (inv_anti₀ (by have := mem_Ioi.mp hx; positivity) (by linarith))) ht

abbrev Square (ι : Type*) := Matrix ι ι ℝ
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Square ι}

omit [Fintype ι] in
lemma scalar_diagonal (u : ℝ) : u • (1 : Square ι) = diagonal (fun _ => u) := by
  ext i j; by_cases i=j <;> simp [*, Matrix.diagonal, one_apply]
omit [Fintype ι] in
lemma shift_posDef (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) : (A+u • 1).PosDef := by
  rw [scalar_diagonal]; exact hA.add_posSemidef (.diagonal fun _ => hu)

private lemma spectrum_shift (hA : A.PosDef) (u : ℝ) :
    let h := hA.1
    let U := conjStarAlgAut ℝ _ h.eigenvectorUnitary
    A + u • 1 = U (diagonal fun i => h.eigenvalues i+u) := by
  intro h U
  have he : A=U (diagonal h.eigenvalues) := h.spectral_theorem
  rw [show diagonal (fun i => h.eigenvalues i+u) = diagonal h.eigenvalues + u • (1:Square ι) by
    rw [scalar_diagonal, ← Matrix.diagonal_add], map_add, map_smul, map_one, ← he]

private lemma spectrum_inverse (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    let h := hA.1
    resolve A u = conjStarAlgAut ℝ _ h.eigenvectorUnitary (diagonal fun i => (h.eigenvalues i+u)⁻¹) := by
  intro h
  apply Matrix.inv_eq_right_inv
  have hl (i : ι) : h.eigenvalues i + u ≠ 0 := (add_pos_of_pos_of_nonneg (hA.eigenvalues_pos _) hu).ne'
  let U := conjStarAlgAut ℝ _ h.eigenvectorUnitary
  rw [spectrum_shift hA u, ← map_mul]
  change U _ = _
  rw [diagonal_mul_diagonal]
  simp [hl]

/-- Resolvent kernel of the logarithm. -/
def density (A : Square ι) (u : ℝ) := attenuation u • (1:Square ι) - resolve A u

/-- The spectral log in E on real PosDef (see `spectralLog`);
use absolute convergence receipts to apply.
No use of the total default of `integral` to claim identities. -/
def logKernel (A : Square ι) : Square ι := Matrix.of fun i j => ∫ u in Ioi 0, density A u i j

lemma density_eigen (hA : A.PosDef) {u : ℝ} (hu : 0 ≤ u) :
    let h := hA.1
    density A u = conjStarAlgAut ℝ _ h.eigenvectorUnitary
      (diagonal fun i => attenuation u - (h.eigenvalues i+u)⁻¹) := by
  intro h
  unfold density; rw [spectrum_inverse hA hu]
  let D : Square ι := diagonal fun i => (h.eigenvalues i + u)⁻¹
  rw [show diagonal (fun i => attenuation u-(h.eigenvalues i+u)⁻¹) = attenuation u • 1 - D by
    unfold D; rw [scalar_diagonal, ← diagonal_sub], map_sub,map_smul,map_one]

lemma conjugate_entry (U : Matrix.unitaryGroup ι ℝ) (d : ι → ℝ) (i j : ι) :
    conjStarAlgAut ℝ _ U (diagonal d) i j = ∑ k, (U.val i k * U.valᴴ k j)*d k := by
  change (U.val * Matrix.diagonal d * U.valᴴ) i j = _
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal]; apply Finset.sum_congr rfl; intros; ring

lemma logEntry_formula (hA : A.PosDef) (i j) :
    let h := hA.1
    IntegrableOn (fun u => density A u i j) (Ioi 0) ∧
      logKernel A i j = conjStarAlgAut ℝ _ h.eigenvectorUnitary (diagonal fun k => Real.log (h.eigenvalues k)) i j := by
  intro h
  let U := h.eigenvectorUnitary
  let g (k : ι) := U.val i k * U.valᴴ k j
  let f k u := g k * (attenuation u - (h.eigenvalues k+u)⁻¹)
  have he : EqOn (fun u => ∑ k,f k u) (fun u => density A u i j) (Ioi 0) := by
    intro u hu; change (∑ k,f k u)=density A u i j; rw [density_eigen hA hu.out.le]
    exact (conjugate_entry U _ i j).symm
  have ht k : Integrable (f k) (volume.restrict (Ioi 0)) := (log_scalar (hA.eigenvalues_pos k)).1.const_mul (g k)
  refine ⟨IntegrableOn.congr_fun (integrable_finsetSum _ (fun k _ => ht k)) he measurableSet_Ioi,?_⟩
  rw [logKernel, of_apply, setIntegral_congr_fun measurableSet_Ioi he.symm,integral_finsetSum _ fun k _ => ht k,
    conjugate_entry]
  apply Finset.sum_congr rfl
  intro k _
  unfold f; rw [integral_const_mul,(log_scalar (hA.eigenvalues_pos k)).2]

/-- Hence exactly the real-positive-spectrum matrix log. -/
theorem spectralLog (hA : A.PosDef) :
    logKernel A = conjStarAlgAut ℝ _ hA.1.eigenvectorUnitary (diagonal fun i => Real.log (hA.1.eigenvalues i)) := by
  ext i j; exact (logEntry_formula hA ..).2

lemma log_trace (hA : A.PosDef) : Real.log A.det = ∑ i : ι, logKernel A i i := by
  let U := hA.1.eigenvectorUnitary
  let D := diagonal fun i => Real.log (hA.1.eigenvalues i)
  rw [spectralLog hA, hA.1.det_eq_prod_eigenvalues]
  change Real.log (∏ i : ι,hA.1.eigenvalues i) = Matrix.trace (U.val*D*U.valᴴ)
  rw [Real.log_prod (fun i _ => (hA.eigenvalues_pos _).ne'), Matrix.trace_mul_comm,← Matrix.mul_assoc,
    show U.valᴴ*U.val=1 from U.prop.1, Matrix.one_mul, Matrix.trace_diagonal]






end YM.AnalyticBridge.RelativeLogdet
