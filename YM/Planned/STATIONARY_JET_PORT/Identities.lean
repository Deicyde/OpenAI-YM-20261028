import YM.Planned.STATIONARY_JET_PORT.Cable
import YM.Push.STATIONARY_UNIFORM.Response

set_option warningAsError false

/-!
# Actual finite period calculus of inverse and log determinant

Entrywise (no estimate for an extensive matrix in a Frobenius norm).
Log is real on the positive collar of interest. Jacobi orientation made
explicit, no diagonalization through repeated eigenvalues.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push.Uniform Filter Function Set Metric Lattice Matrix
open scoped Topology ContDiff BigOperators Classical
variable {ι τ σ π : Type} [Fintype ι] [Fintype σ] [DecidableEq σ]
    {M : Positions ι → Matrix σ σ ℝ} {x : Positions ι}

lemma bornMatrix.determinant (h : bornMatrix M x) : ContDiffAt ℝ ω (fun y => (M y).det) x := by
  simp_rw [det_apply']; exact ContDiffAt.sum fun i _ => contDiffAt_const.mul (contDiffAt_prod fun j _ => h _ _)

lemma bornMatrix.inverse (h : bornMatrix M x) (he : (M x).det ≠ 0) : bornMatrix (fun y => (M y)⁻¹) x := by
  intro i j
  simp_rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, adjugate_apply]
  refine (h.determinant.inv he).smul (bornMatrix.determinant (M:=fun y => (M y).updateRow j _) ?_)
  intro a b; by_cases hv : a=j
  · subst a; simpa using! (contDiffAt_const (𝕜:=ℝ) (x:=x) (n:=ω) (c:=((Pi.single i 1 : σ → ℝ) b)))
  simpa only [Matrix.updateRow_ne hv] using h a b

lemma bornMatrix.shares (h : bornMatrix M x) (he : (M x).det ≠ 0) :
    ∀ᶠ y in 𝓝 x, bornMatrix M y ∧ (M y).det ≠ 0 := by
  refine (eventually_and.mpr ⟨?_, h.determinant.continuousAt.eventually_ne he⟩)
  change ∀ᶠ y in 𝓝 x, ∀ i j, _
  simp_rw [eventually_all]; intro i j; exact (h i j).eventually (by simp)

/-- Directional matrix derivative; order of indices UNCHANGED. -/
def finger (F : Positions ι → Matrix τ π ℝ) (d : ι) (x : Positions ι) := Matrix.of fun i j =>
    coordinate (fun y => F y i j) d x
omit [Fintype σ] [DecidableEq σ] in
lemma bornMatrix.finger {F : Positions ι → Matrix τ π ℝ} (h : bornMatrix F x) (d : ι) : bornMatrix (JetPort.finger F d) x :=
  fun i j => ((h i j).fderiv_right (m:=ω) (by simp)).clm_apply contDiffAt_const
omit [DecidableEq σ] in
lemma first_matrix {F : Positions ι → Matrix τ σ ℝ} {G : Positions ι → Matrix σ π ℝ}
    (hF : bornMatrix F x) (hG : bornMatrix G x) (d : ι) :
    finger (fun y => F y * G y) d x = F x * finger G d x + finger F d x * G x := by
  ext i j
  unfold finger coordinate
  simp only [of_apply,Matrix.mul_apply,Matrix.add_apply]
  rw [← Finset.sum_add_distrib, fderiv_fun_sum,_root_.sum_apply]
  · apply Finset.sum_congr rfl; intro k _
    rw [fderiv_fun_mul ((hF _ _).differentiableAt (by simp)) ((hG _ _).differentiableAt (by simp))]
    simp [add_comm,mul_comm]
  exact fun _ _ => ((hF _ _).mul (hG _ _)).differentiableAt (by simp)

omit [Fintype ι] in
lemma const_matrix (T : Matrix τ π ℝ) (d : ι) (x : Positions ι) : finger (fun _ => T) d x = 0 := by
  ext i j; simp [finger, coordinate]

lemma inverse_germ (hM : bornMatrix M x) (he : (M x).det ≠ 0) (d : ι) :
    let H (y) := (M y)⁻¹
    finger H d =ᶠ[𝓝 x] fun y => -(H y * finger M d y * H y) := by
  intro H
  have hh := hM.shares he
  filter_upwards [hh,eventually_eventually_nhds.mpr hh] with y hy hv
  have ht : finger (fun u => M u * H u) d y = 0 := by
    rw [← const_matrix (1 : Matrix σ σ ℝ) d y]; ext i j
    unfold finger coordinate; simp only [of_apply]
    have hf : (fun u => (M u * H u) i j) =ᶠ[𝓝 y] (fun _ => (1 : Matrix σ σ ℝ) i j) := hv.mono fun u hu => by
      dsimp only; rw [Matrix.mul_nonsing_inv (M u) (isUnit_iff_ne_zero.mpr hu.2)]
    rw [hf.fderiv_eq]
  rw [first_matrix hy.1 (hy.1.inverse hy.2) d] at ht
  change finger H d y = _
  have h := congr_arg (fun z => H y * z) ht
  rw [Matrix.mul_add, ← Matrix.mul_assoc, show H y * M y = 1 from Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hy.2),
    Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h

-- Jacobi at the identity by routed real derivative of the permutation
-- polynomial (permutation convention of Matrix; no division by dimension).
private lemma det_first (hM : bornMatrix M x) (h : M x=1) (d : ι) :
    coordinate (fun y => (M y).det) d x = Matrix.trace (finger M d x) := by
  let e (s : Equiv.Perm σ) : ℝ := ↑(↑(Equiv.Perm.sign s) : ℤ)
  let E s (y : Positions ι) : ℝ := e s * ∏ i, M y (s i) i
  have he (s : Equiv.Perm σ) : DifferentiableAt ℝ (fun y => ∏ i, M y (s i) i) x :=
    (contDiffAt_prod (t:=Finset.univ) (fun i _ => hM _ _)).differentiableAt (by simp)
  unfold coordinate
  simp_rw [det_apply']; change fderiv ℝ (fun y => ∑ s, E s y) x _ = _
  rw [fderiv_fun_sum (A:=E) (u:=Finset.univ) (fun s _ => (differentiableAt_const _).mul (he s)),_root_.sum_apply,Finset.sum_eq_single (1 : Equiv.Perm σ)]
  · rw [show E (1 : Equiv.Perm σ) = (fun y => ∏ i, M y i i) by funext; simp [E,e]]
    rw [fderiv_finsetProd (u:=Finset.univ) (g:=fun i y => M y i i) (fun i _ => (hM i i).differentiableAt (by simp)),_root_.sum_apply]
    apply Finset.sum_congr rfl; intro i _
    rw [h]; simp [finger,coordinate]
  · intro s _ hs
    have empty (i : σ) : ∃ j : σ, j≠i ∧ s j ≠ j := by
      by_contra! hh
      apply hs; ext j; by_cases hk : s j = j
      · exact hk
      have hk' : s j≠i ∨ j≠i := by by_contra! he; exact hk (he.1.trans he.2.symm)
      rcases hk' with H|H
      · exact (hk ((s.injective (hh (s j) H)))).elim
      exact hh j H
    unfold E
    rw [fderiv_fun_mul (d:=fun y => ∏ i, M y (s i) i) (𝕜:=ℝ) (c:=fun _ => e s)
      (differentiableAt_const _) (he s), fderiv_const_apply,
      fderiv_finsetProd (u:=Finset.univ) (g:=fun i y => M y (s i) i) (fun i _ => (hM _ _).differentiableAt (by simp)),
      Finset.sum_eq_zero (s:=Finset.univ) (fun i _ => ?_)]
    · simp
    rw [h]
    obtain ⟨j,hj,hJ⟩ := empty i
    rw [Finset.prod_eq_zero (f:=fun j : σ => (1 : Matrix σ σ ℝ) (s j) j) (Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩) (Matrix.one_apply_ne (α:=ℝ) hJ), zero_smul]
  simp

theorem log_germ (hM : bornMatrix M x) (he : (M x).det ≠ 0) (d : ι) :
    coordinate (fun y => Real.log (M y).det) d =ᶠ[𝓝 x] fun y => Matrix.trace ((M y)⁻¹ * finger M d y) := by
  filter_upwards [hM.shares he] with y hy
  have hf := hy.1
  let b := (M y).det
  let R := (M y)⁻¹
  have hi := isUnit_iff_ne_zero.mpr hy.2
  let N (x) := R * M x
  have hR : bornMatrix (fun _ : Positions ι => R) y := fun _ _ => contDiffAt_const
  have hN := hR.multiply hf
  have ht := det_first hN ((M y).nonsing_inv_mul hi) d
  have hh : finger N d y=R* finger M d y := by rw [first_matrix hR hf d,const_matrix,Matrix.zero_mul,add_zero]
  have h₀ : (fun z => (M z).det) = (fun z => b * (N z).det) := by
    funext z; unfold N R b; rw [det_mul, ← mul_assoc,mul_comm (M y).det, Matrix.det_nonsing_inv_mul_det _ hi,one_mul]
  have hD := hf.determinant.differentiableAt (by simp)
  change fderiv ℝ (fun z => Real.log (M z).det) y (bolt d) = _
  rw [(hD.hasFDerivAt.log hy.2).fderiv]; change b⁻¹ * coordinate (fun z => (M z).det) d y = _ -- check beta
  rw [h₀,show coordinate (fun z => b * (N z).det) d y = b * coordinate (fun z => (N z).det) d y by
    unfold coordinate; rw [fderiv_fun_mul (c:=fun z => b) (d:=fun z => (N z).det) (differentiableAt_const b)
      (hN.determinant.differentiableAt (by simp)), fderiv_const_apply]; simp,
    inv_mul_cancel_left₀ hy.2, ht, hh]
end YM.Planned.JetPort
