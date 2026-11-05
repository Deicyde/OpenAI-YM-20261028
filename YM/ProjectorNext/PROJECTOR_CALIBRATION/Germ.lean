import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct

/-! # Divide out one amplitude per required zero factor, through finite jets

Stay entirely finite. Smooth at zero is enough on the **actual Snap response**
(no uniform ODE radius); replace it by finite Taylor on Snap before extracting
the engine coefficient. Division here is amplitude (`θ`), NOT powers of h.
Use one spare Taylor order at d=0 so the divided law is actually defined
with the same first-order meaning also there. Supports in Unpack already
paid so this calculation on the cover controls the actual amount.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration.Coupon
open Function Filter Tensor Work Next.Foundations
open scoped Topology BigOperators ContDiff
variable {X Y V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] (d : ℕ)

/-- (Taylor to d+1, nonconstant terms) with one amplitude removed. -/
def trim (Z : X → Y) (θ : ℝ) (A : X) :=
    ∑ j∈Finset.range (d+1), θ^j • Tensor.diagonal (Tensor.coeff Z (j+1) 0) A

lemma block_eq (Z : X → Y) (θ : ℝ) (A : X) :
    G05.blockTaylor (d+1) Z (θ • A) = Z 0 + θ • trim d Z θ A := by
  rw [G05.blockTaylor,Finset.sum_apply,Finset.sum_range_succ']
  rw [show Tensor.diagonal (Tensor.coeff Z 0 0) (θ • A)=Z 0 from Tensor.coeff_apply_zero ..]
  simp_rw [trim, Tensor.homogeneous,Finset.smul_sum,smul_smul,pow_succ',add_comm (Z 0)]

lemma trim_value (Z : X → Y) (A : X) : trim d Z 0 A = fderiv ℝ Z 0 A := by
  rw [trim, Finset.sum_range_succ']
  simp only [zero_pow (Nat.succ_ne_zero _), zero_smul,Finset.sum_const_zero, pow_zero,one_smul,zero_add]
  unfold Tensor.diagonal Tensor.coeff
  simp [iteratedFDeriv_one_apply]

lemma trim_smooth (Z : X → Y) : ContDiff ℝ ω (uncurry (trim d Z)) := by
  refine ContDiff.sum (f:=fun i (p : ℝ × X) => p.1^i • Tensor.diagonal (Tensor.coeff Z (i+1) 0) p.2) (s:=Finset.range (d+1)) ?_
  intro i _; exact (contDiff_fst.pow _).smul ((diag_smooth _ _).comp contDiff_snd)

/-- Compose a sensor `P` and a path in Snap, replacing only the Snap
response, preserving k=h jet (parameter fixed). -/
lemma exchanged {k : ℕ} (hk : k≤d+1) {Z : X → Y} {P : Y → V} {r : ℝ → X} (θ : ℝ)
    (hZ : ContDiffAt ℝ ω Z 0) (hP : ContDiff ℝ ω P) (hr : ContDiff ℝ ω r) (he : r 0=0) :
    iteratedDeriv k (fun h : ℝ => P (Z (θ • r h))) 0 =
      iteratedDeriv k (fun h => P (Z 0+θ • trim d Z θ (r h))) 0 := by
  let f (t : ℝ) := θ • r t
  have hf : ContDiff ℝ (↑(d+1:ℕ)) f := (contDiff_const (c:=θ)).smul (hr.of_le le_top)
  have hz : f 0=0 := by simp [f,he]
  have hu : ContDiffAt ℝ (↑(d+1:ℕ)) Z 0 := hZ.of_le le_top
  let Y₀ := G05.blockTaylor (d+1) Z
  have hv : ContDiff ℝ (↑(d+1:ℕ)) Y₀ := G05.blockTaylor_contDiff ..
  have hL := hP.of_le (show (↑(d+1:ℕ) : WithTop ℕ∞) ≤ ω from le_top)
  have ht : iteratedFDeriv ℝ k ((P ∘ Z) ∘ f) 0 = iteratedFDeriv ℝ k ((P ∘ Y₀) ∘ f) 0 := by
    refine G05.jets_comp (d:=d+1) hf.contDiffAt hf.contDiffAt ?_ (hL.comp hv).contDiffAt rfl (fun _ _ => rfl) ?_ k hk
    · rw [hz]; exact hL.contDiffAt.comp 0 hu
    rw [hz]; exact G05.jets_comp hu hv.contDiffAt hL.contDiffAt hL.contDiffAt (G05.blockTaylor_zero ..).symm (fun j hj => (G05.blockTaylor_jets hu j hj).symm) (fun _ _ => rfl)
  simp_rw [← block_eq]
  exact congr_arg (fun T : Tensor.T ℝ V k => T fun _ => (1:ℝ)) ht

lemma sensed {Z : X → Y} {P : Y → V} {r : ℝ → X} (θ : ℝ)
    (hZ : ContDiffAt ℝ ω Z 0) (hP : ContDiff ℝ ω P) (hr : ContDiff ℝ ω r) (he : r 0=0) :
    ContDiffAt ℝ ω (fun h => P (Z (θ • r h))) 0 := by
  let f (t : ℝ) := θ • r t
  have hh : ContDiffAt ℝ ω (P ∘ Z) (f 0) := by rw [show f 0=0 from (by simp [f,he])]; exact hP.contDiffAt.comp 0 hZ
  exact hh.comp (0:ℝ) (((contDiff_const (c:=θ)).smul hr).contDiffAt (x:=0))

/-- Continuity of finite h jets of any precalculated smooth law with respect
to the parameters. -/
private lemma vary {f : X × ℝ → Y} (h : ContDiff ℝ ω f) (k : ℕ) :
    ContDiff ℝ ω (fun p : X × ℝ => iteratedDeriv k (fun t => f (p.1,t)) p.2) := by
  induction k with
  | zero => simpa only [iteratedDeriv_zero] using h
  | succ k ih =>
    let A (p : X × ℝ) (t : ℝ) := iteratedDeriv k (fun r => f (p.1,r)) t
    have he : ContDiff ℝ ω (fun p : X × ℝ => fderiv ℝ (A p) p.2) := ContDiff.fderiv (m:=ω)
      (ih.comp (f:=fun p : (X × ℝ) × ℝ => (p.1.1,p.2)) (by fun_prop)) contDiff_snd (by simp)
    simp_rw [iteratedDeriv_succ]
    exact he.clm_apply (g:=fun _ => (1:ℝ)) contDiff_const

lemma varies (k : ℕ) {f : X × ℝ → Y} (h : ContDiff ℝ ω f) :
    ContDiff ℝ ω (fun p : X => iteratedDeriv k (fun t => f (p,t)) 0) :=
  (vary h k).comp (f:=fun p => (p,0)) (contDiff_id.prodMk contDiff_const)

end YM.ProjectorNext.Calibration.Coupon
