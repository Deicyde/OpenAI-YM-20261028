import YM.Bid.Loan
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Strings

set_option warningAsError false

/-!
# Averaged direction: identity modulo one lower degree. Gradients
and radial tensors. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Averaging
open Function Filter Finset Tensor Work Set MeasureTheory Powers Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Mean on the segment, defined as in the Volterra tool via projIcc. -/
def average : C(unitInterval,E) →L[ℝ] E := by
  let π := projIcc (0:ℝ) 1 zero_le_one
  have hf (v : C(unitInterval,E)) : IntervalIntegrable (fun t => v (π t)) volume 0 1 :=
    (v.continuous.comp continuous_projIcc).intervalIntegrable _ _
  let A : C(unitInterval,E) →ₗ[ℝ] E := {
    toFun v := ∫ t in (0:ℝ)..1,v (π t)
    map_add' v u := intervalIntegral.integral_add (hf v) (hf u)
    map_smul' r u := by change (∫ t in (0:ℝ)..1,r • u (π t))= r • (∫ t in (0:ℝ)..1,u (π t)); rw [intervalIntegral.integral_smul] }
  refine A.mkContinuous 1 fun v => ?_
  rw [one_mul]; change ‖∫ t in (0:ℝ)..1,v (π t)‖ ≤ _
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (f:=fun t => v (π t)) (fun s _ => v.norm_coe_le_norm (π s))

omit [FiniteDimensional ℝ E] in -- maybe
lemma integrated (f : C(unitInterval,E)) (p : ℝ → E) (h : ∀ t : unitInterval, f t=p t) :
    average f=∫ t in (0:ℝ)..1,p t := by
  let π := projIcc (0:ℝ) 1 zero_le_one
  change (∫ t in (0:ℝ)..1,f (π t)) = _
  refine intervalIntegral.integral_congr (fun i hi => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hi; unfold π; rw [projIcc_of_mem _ hi,h]

lemma buys {k : ℕ} {p : V → E} (h : home p k) (x : V) :
    (fun v : V => (∫ t in (0:ℝ)..1,p (v+t • x))-p v) ∈ space V E (k-1) := by
  let A := Tensor.coeff p k 0
  letI := FiniteDimensional.complete ℝ E
  convert carried average (sparse_mem A x) using 1
  funext v
  have hv : IntervalIntegrable (fun t : ℝ => p (v+t • x)) volume 0 1 := (h.1.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).intervalIntegrable _ _
  rw [integrated (sparse A x v) (fun t => p (v+t • x)-p v) (fun t => ?_), intervalIntegral.integral_sub hv intervalIntegrable_const,intervalIntegral.integral_const]; simp
  rw [tensor_form h,diag_sparse,add_sub_cancel_left]


variable {p : V → E} {k : ℕ}
omit [FiniteDimensional ℝ E] in
lemma graded (h : home p (k+1)) (y : V) : home (D y p) k := by
  let A := Tensor.coeff p (k+1) 0
  let i (v) := (A.curryLeft v)
  have hp : p=Tensor.diagonal A := tensor_form h
  have hv v : D y p v=((k+1):ℕ) • Tensor.diagonal (i y) v := by
    change fderiv ℝ p v y = _
    rw [hp,Tensor.differential_diagonal A (Tensor.coeff_symm (h.1.contDiffAt.of_le le_top))]
    rfl
  rw [funext hv]
  refine ⟨?_,fun t v => ?_⟩
  · simp_rw [← Nat.cast_smul_eq_nsmul ℝ]; exact contDiff_const.smul (diag_smooth ..)
  dsimp only; rw [homogeneous, ← Nat.cast_smul_eq_nsmul ℝ,← Nat.cast_smul_eq_nsmul ℝ]; exact smul_comm ..

lemma differential (h : home p (k+1)) (x : V) (v : V) :
    (∫ t : ℝ in 0..1, D x p (v+t • x))=p (v+x)-p v := by
  letI := FiniteDimensional.complete ℝ E
  conv_rhs => rw [← one_smul ℝ x]; rhs; rw [← add_zero v, ← zero_smul ℝ x]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun t : ℝ => p (v+t • x))
    (fun y _ => ((h.1.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt y (show HasDerivAt (fun t => v+t • x) x y by simpa using ((hasDerivAt_id' y).smul_const x).const_add v)))
    (((graded h x).1.continuous.comp (by fun_prop : Continuous (fun t : ℝ => v+t • x))).intervalIntegrable _ _)

open Lattice
private lemma basis_sum (x : E4) : (∑ i : Axis, x i • basis i) = x := by
  -- from standard basis
  let g := EuclideanSpace.basisFun Axis ℝ
  simpa only [g, EuclideanSpace.basisFun_repr,EuclideanSpace.basisFun_apply,basis] using g.sum_repr x

/-- Every positive-degree homogeneous vector splits as a true radial jet
 plus sampled gradient homogeneous. (The degree 0 is entirely gradient --
 handle separately.) Compatible with the genuine `Labels.radial` curve and
 the grading there (Snap i really degree i+1). -/
lemma locale {G : Gauge} {Q : Axis → E4 → G.Color} (j) (h : ∀ i, home (Q i) (j+1)) :
    ∃ (r : E4→G.Color) (K : Labels.Taylor G j), home r (j+2) ∧ ∀ i v,Q i v=K.value i v + D (basis i) r v := by
  let w := (j+2:ℝ)
  let p (x : E4) := ∑ i, x i • Q i x
  let R := w⁻¹ • p
  have hw : w = (j+2:ℕ) := by push_cast; rfl
  have h0 : w ≠ 0 := by rw [hw]; positivity
  have hr : home p (j+2) := by
    refine ⟨ContDiff.sum (fun i _ => ?_), fun t v => ?_⟩
    · exact (EuclideanSpace.proj _).contDiff.smul (h i).1
    unfold p; rw [Finset.smul_sum]; refine sum_congr rfl fun i _ => ?_
    rw [(h i).2,smul_smul]; simp only [PiLp.smul_apply,smul_eq_mul,smul_smul]; congr 1; ring
  have hR : home R (j+2) := ⟨contDiff_const.smul hr.1, fun t v => by simp [R,hr.2]; exact smul_comm ..⟩
  let L i v := Q i v-D (basis i) R v
  let T (i : Axis) := Tensor.coeff (L i) (j+1) 0
  have ht i : home (D (basis i) R) (j+1) := graded hR _
  have hl i : home (L i) (j+1) := ⟨(h i).1.sub (ht i).1, fun t v => by unfold L; rw [(h i).2,(ht i).2,smul_sub]⟩
  have hh i : L i=Tensor.diagonal (T i) := tensor_form (hl i)
  have hv : T∈Labels.radial G j := by
    refine ⟨fun i => Tensor.coeff_symm ((hl i).1.contDiffAt.of_le le_top),fun x => ?_⟩
    have hp : (fderiv ℝ R x) x=p x := by
      let r := Tensor.coeff R (j+2) 0
      have hT : R=Tensor.diagonal r := tensor_form hR
      rw [hT, Tensor.Euler r (Tensor.coeff_symm (hR.1.contDiffAt.of_le le_top)), ← hT,← hw]
      simp only [R,Pi.smul_apply,
        smul_inv_smul₀ h0]
    simp_rw [← hh,L,smul_sub, Finset.sum_sub_distrib, D, ← map_smul, ← map_sum, basis_sum]
    exact sub_eq_zero.mpr hp.symm
  refine ⟨R,⟨T,hv⟩,hR,fun i x => ?_⟩
  change _=Tensor.diagonal (T i) x+_
  rw [← hh]; unfold L; exact (sub_add_cancel ..).symm

lemma sheet0 {G : Gauge} {Q : Axis → E4 → G.Color} (h : ∀ i, home (Q i) 0) :
    ∃ r : E4→G.Color,home r 1 ∧ ∀ i v,Q i v=D (basis i) r v := by
  let T : E4 →L[ℝ] G.Color := ∑ i,(EuclideanSpace.proj i).smulRight (Q i 0)
  refine ⟨T,⟨T.contDiff,fun i v => by rw [map_smul,pow_one]⟩,fun i v => ?_⟩
  have hh := (h i).2 0 v; simp at hh
  unfold D; rw [T.fderiv,_root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply,EuclideanSpace.proj,basis]; simp [hh]
end YM.MultiNext.SignedSource.Averaging
