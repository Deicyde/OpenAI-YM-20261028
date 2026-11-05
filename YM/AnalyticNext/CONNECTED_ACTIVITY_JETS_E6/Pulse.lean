import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter

/-!
# Logarithmic Jacobi at real counting units

We use compact glide integrals instead of spectral L-shaped resolvent
integral. Sets up actual local log-letters and *small* chain labels.
Not interpreting log integrals as replacing full A by principal windows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Pulse
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical Polynomial
variable {c : Side} {ι : Type*} {a : ι→Site c} {B : ℕ} (D : Window a B) [DecidableEq ι] [Fintype ι]
variable (A : Matrix ι ι ℝ)

private lemma deriv_trace : HasDerivAt (fun r : ℝ => (1+r • A).det) A.trace 0 := by
  let L := 1+(Polynomial.X (R:=ℝ)) • (A.map (Polynomial.C (R:=ℝ)))
  let P : Polynomial ℝ := L.det
  have he : Polynomial.eval 0 (Polynomial.derivative P) = trace A := Matrix.derivative_det_one_add_X_smul A
  have hh (r : ℝ) : Polynomial.eval r P=(1+r • A).det := by
    let W := Polynomial.evalRingHom r
    change W L.det=(1+r • A).det
    rw [RingHom.map_det]; congr 1
    unfold L; rw [map_add,map_one]; congr 1; ext i j
    change Polynomial.eval r (Polynomial.X * Polynomial.C (A i j))=r*A i j; simp; ring
  simp_rw [← hh,← he]; exact P.hasDerivAt _

lemma pulse (r : ℝ) (h : glide A r*(glide A r)⁻¹=1) : HasDerivAt (fun s => Real.log (glide A s).det)
    (Matrix.trace ((A-1)*(glide A r)⁻¹)) r := by
  let W := glide A r; let B := (A-1)*W⁻¹
  have hi : IsUnit W.det := Matrix.isUnit_det_of_right_inverse h
  have he (s : ℝ) : glide A s=(1+(s-r) • B)*W := by
    have hb : B*W=A-1 := by unfold B; rw [mul_assoc,Matrix.nonsing_inv_mul W hi,mul_one]
    rw [add_mul,smul_mul_assoc,hb,one_mul]; unfold W glide; rw [sub_smul]; abel
  have hk : HasDerivAt (fun s : ℝ => s-r) 1 r := (hasDerivAt_id' r).sub_const _
  let f s := s-r
  have hu := (show HasDerivAt (fun r=> (1+r • B).det) B.trace (f r) from by unfold f; rw [sub_self]; exact deriv_trace B).comp r hk
  have hF : (fun s => (glide A s).det)= (fun s => (1+(s-r) • B).det * W.det) := by
    funext s; rw [he s, Matrix.det_mul]
  have hz : HasDerivAt (fun s => (glide A s).det) (B.trace * W.det) r := by
    rw [hF]; simpa only [f,Function.comp_def, mul_one] using! hu.mul_const W.det
  simpa only [show glide A r=W from rfl,mul_div_cancel_right₀ _ hi.ne_zero] using! hz.log hi.ne_zero

omit [Fintype ι] in
@[fun_prop] lemma strung : Continuous (glide A) := Continuous.add continuous_const (continuous_id.smul continuous_const)
lemma flowing {W : ℝ → Matrix ι ι ℝ} (U : Set ℝ) (hw : Continuous W) (he : ∀ s∈U, IsUnit (W s).det) :
    ContinuousOn (fun s => (W s)⁻¹) U := by
  simp_rw [Matrix.inv_def,Ring.inverse_eq_inv]; exact ((hw.matrix_det.continuousOn).inv₀
    (fun i hi => (he i hi).ne_zero)).smul hw.matrix_adjugate.continuousOn
omit [DecidableEq ι] in
lemma tracing {W : ℝ → Matrix ι ι ℝ} (U : Set ℝ) (hw : ContinuousOn W U) : ContinuousOn (fun s => trace (W s)) U := by
  have ht := (show Continuous (fun M : Matrix ι ι ℝ => trace M) from continuous_id.matrix_trace)
  exact ht.comp_continuousOn hw
lemma total (h : ∀ s ∈ Set.Icc (0:ℝ) 1, IsUnit (glide A s).det) :
    Real.log A.det = ∫ s in (0:ℝ)..1, Matrix.trace ((A-1)*(glide A s)⁻¹) := by
  let U := Set.uIcc (0:ℝ) 1
  have hf (s) (hs : s∈U) := h s (by unfold U at hs; rwa [Set.uIcc_of_le zero_le_one] at hs)
  have he (s) (hs : s∈U) := pulse A s (Matrix.mul_nonsing_inv _ (hf s hs))
  have ht := intervalIntegral.integral_eq_sub_of_hasDerivAt he
    ((tracing U (W:=fun s => (A-1)*(glide A s)⁻¹) (ContinuousOn.mul continuousOn_const (flowing U (strung _) hf))).intervalIntegrable)
  simp only [glide_end,glide_start, Matrix.det_one,Real.log_one,sub_zero] at ht; exact ht.symm
lemma vibrate {m : ℕ} {η r X : ℝ} (h : Allow A a m η r X) (hp : Torch η r X) :
    ContinuousOn (fun s => D.pad (glide A s)) (Set.uIcc (0:ℝ) 1) := by
  rw [Set.uIcc_of_le zero_le_one]; apply continuousOn_pi.mpr; intro i; apply continuousOn_pi.mpr; intro j
  change ContinuousOn (fun s=> D.pad (glide A s) i j) _
  by_cases he : i∈D.take j
  swap
  · simp_rw [D.outside (glide A _) i j he]; exact continuousOn_const
  let W s := D.principal (glide A s) j
  have hx : Continuous W := (strung _).matrix_submatrix _ _
  have ht : ContinuousOn (fun s => (W s)⁻¹) (Set.Icc (0:ℝ) 1) := flowing _ hx fun s hs =>
    Matrix.isUnit_det_of_right_inverse (((h.glide hp.hv hp.hQ s hs).sub (Embedding.subtype (·∈D.take j))).initial.1)
  simp only [Window.pad,of_apply,dif_pos he]; exact (continuousOn_pi.mp (continuousOn_pi.mp ht ⟨i,he⟩) ⟨j,D.here j⟩)
end YM.ConnectedActivityE6.Pulse
