import YM.Primitives.SMALL_FIELD_EXTERIOR.Faces

/-!
# Neumann class and weighted cube IBP

Include the tangential face equations explicitly on the core of **tests for
the Poisson problem**. We will have dense range even with these hypotheses on
the tests. Observables for the covariance inequality DON'T need them.
Use total negative log potential V, including even the Gaussian part.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.SmallFieldExterior
open Function Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {i j : ι} {V u v : Points ι → ℝ} {c r : ℝ}

structure Neumann (r : ℝ) (u : Points ι → ℝ) : Prop where
  smooth : ContDiff ℝ ω u
  normal (i : ι) (x : Points ι) : x ∈ cube ι r → |x i|=r → pc i u x=0
  mixed (i j : ι) : i≠j → ∀ x∈cube ι r, |x i|=r → pc i (pc j u) x=0

namespace Neumann
variable (h : Neumann r u)
include h
lemma differential {x : Points ι} : DifferentiableAt ℝ u x := h.smooth.differentiable (by simp) x
lemma stripe (i : ι) {n : ℕ∞ω} : Regular r n (pc i u) := fun _ _ =>
  (pcat i h.smooth.contDiffAt (k:=ω) (by simp)).of_le le_top
lemma reg {n : ℕ∞ω} : Regular r n u := fun _ _ => h.smooth.contDiffAt.of_le le_top
lemma swap (i j : ι) : pc i (pc j u)=pc j (pc i u) := funext fun _ => pc_comm i j (h.smooth.contDiffAt.of_le le_top)
lemma add (h' : Neumann r v) : Neumann r (u+v) := by
  have he i : pc i (u+v)=pc i u + pc i v := funext fun _ => pc_plus i h.differential h'.differential
  refine ⟨h.smooth.add h'.smooth, fun i x hx hh => ?_, fun i j hi x hx hh => ?_⟩
  · rw [he, Pi.add_apply,h.normal i x hx hh,h'.normal i x hx hh,add_zero]
  rw [he, pc_plus i ((h.stripe j).diff one_ne_zero hx) ((h'.stripe j).diff one_ne_zero hx), h.mixed i j hi x hx hh, h'.mixed i j hi x hx hh,add_zero]
lemma smul (c : ℝ) : Neumann r (c • u) := by
  have he i : pc i (c • u)= c • pc i u := funext fun _ => pc_smul i c h.differential
  refine ⟨contDiff_const.smul h.smooth, fun i x hx hh => ?_, fun i j hi x hx hh => ?_⟩
  · rw [he, Pi.smul_apply, h.normal i x hx hh, smul_zero]
  rw [he, pc_smul i c ((h.stripe j).diff one_ne_zero hx), h.mixed i j hi x hx hh,mul_zero]
omit h
lemma const (c : ℝ) : Neumann r (fun _ : Points ι => c) :=
  ⟨contDiff_const,fun _ _ _ _ => by simp [pc],fun _ _ _ _ _ _ => by rw [pc_const, show (0:Points ι → ℝ)=fun _ => (0:ℝ) from rfl, pc_const]; rfl⟩
end Neumann

/-- Component of the positive-sign Neumann generator. -/
def row (V : Points ι → ℝ) (i : ι) (u : Points ι → ℝ) : Points ι → ℝ := pc i V * pc i u - pc i (pc i u)
def elliptic (V : Points ι → ℝ) (u : Points ι → ℝ) := ∑ i, row V i u

lemma Neumann.row1 (hu : Neumann r u) (hV : Regular r 2 V) (i : ι) : Regular r 1 (row V i u) :=
  ((hV.tangent i).mul (hu.stripe i)).sub ((hu.stripe i).tangent i)
lemma Neumann.elliptic1 (hu : Neumann r u) (hV : Regular r 2 V) : Regular r 1 (elliptic V u) :=
  Regular.fsum _ fun i _ => hu.row1 hV i

lemma elliptic_add (V : Points ι → ℝ) (hu : Neumann r u) (hv : Neumann r v) :
    elliptic V (u+v)=elliptic V u+elliptic V v := by
  have he (i : ι) : pc i (u+v)=pc i u+pc i v := funext fun _ => pc_plus _ hu.differential hv.differential
  unfold elliptic; rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ => funext (fun x => ?_)
  unfold row; rw [he]; simp only [Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
  rw [pc_plus i ((pcat i hu.smooth.contDiffAt (k:=ω) (by simp)).differentiableAt (by simp))
    ((pcat i hv.smooth.contDiffAt (k:=ω) (by simp)).differentiableAt (by simp))]; ring
lemma elliptic_smul (V : Points ι → ℝ) (hu : Neumann r u) (c : ℝ) :
    elliptic V (c • u)=c • elliptic V u := by
  have he (i : ι) : pc i (c • u)=c • pc i u := funext fun _ => pc_smul _ c hu.differential
  unfold elliptic; rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _ => funext (fun x => ?_)
  unfold row; rw [he]; simp only [Pi.smul_apply,Pi.mul_apply,Pi.sub_apply, smul_eq_mul]
  rw [pc_smul i c ((pcat i hu.smooth.contDiffAt (k:=ω) (by simp)).differentiableAt (by simp))]; ring
lemma elliptic_zero (V : Points ι → ℝ) : elliptic V 0=0 := by
  unfold elliptic row
  have hc i : pc i (0:Points ι → ℝ) = 0 := pc_const i 0
  simp [hc]

/-- IBP in direction i including when the factor multiplying the normal
derivative vanishes on the face. Use this also at edge/corner points in the
iteration below. No assumptions on global smooth extension of the cutoff
indicator. -/
lemma move_row (hr : 0 ≤ r) (hV : Regular r 1 V) (hu : Regular r 2 u) (hf : Regular r 1 v)
    (h : ∀ x∈cube ι r, |x i|=r → pc i u x * v x=0) : bracket r V (row V i u) v = bracket r V (pc i u) (pc i v) := by
  let R := fun x => Real.exp (-V x)
  have hi := hu.tangent i
  have hR : Regular r 1 R := fun x hx => (((hV x hx).neg).exp)
  have he := (hR.mul hi).mul hf
  have hx : (∫ x in cube ι r, pc i (R * pc i u * v) x) = 0 := faces_zero hr he i fun x hx h' => by
    change R x * pc i u x * v x=0; rw [mul_assoc,h x hx h',mul_zero]
  have ht : EqOn (pc i (R * pc i u * v)) (fun x => Real.exp (-V x) * (((pc i u)*(pc i v)) x - (row V i u * v) x)) (cube ι r) := by
    intro x hx
    have hRR := hR.diff one_ne_zero hx; have hi' := hi.diff one_ne_zero hx
    rw [pc_mul _ (hRR.mul hi') (hf.diff one_ne_zero hx), pc_mul _ hRR hi', show pc i R x=_ from pc_exp_neg i (hV.diff one_ne_zero hx)]
    simp only [row, R, Pi.sub_apply, Pi.mul_apply]
    ring
  rw [setIntegral_congr_fun (cube_meas _) ht] at hx
  have hv : ContinuousOn (row V i u) (cube ι r) := ((hV.tangent_continuous i).mul hi.cOn).sub (hi.tangent_continuous i)
  change raw r V ((pc i u)*(pc i v)-row V i u * v)=0 at hx
  rw [raw_sub hV.cOn (hi.cOn.mul (hf.tangent_continuous i)) (hv.mul hf.cOn),sub_eq_zero] at hx
  exact hx.symm

lemma Neumann.by_row (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 1 V) (hf : Regular r 1 v) (i : ι) :
    bracket r V (row V i u) v = bracket r V (pc i u) (pc i v) :=
  move_row hr hV hu.reg hf fun x hx h => by rw [hu.normal i x hx h,zero_mul]

lemma Neumann.energy (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (hf : Regular r 1 v) :
    bracket r V (elliptic V u) v = ∑ i, bracket r V (pc i u) (pc i v) := by
  unfold elliptic
  rw [bracket_sum hV.cOn _ (fun i _ => (hu.row1 hV i).cOn) hf.cOn]
  exact Finset.sum_congr rfl fun i _ => hu.by_row hr (hV.mono (by norm_num)) hf i
lemma Neumann.mean_zero (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (c : ℝ) :
    bracket r V (elliptic V u) (fun _ => c) = 0 := by
  rw [hu.energy hr hV (Regular.coefficient c)]; simp [pc_const,bracket,raw]

/-- The actual commutator, an entry of the physical Hessian. -/
lemma Neumann.commute (hu : Neumann r u) (hV : Regular r 2 V) (i j : ι) :
    EqOn (pc i (row V j u)) (row V j (pc i u) + pc i (pc j V) * pc j u) (cube ι r) := by
  intro x hx
  have he := (hu.stripe j).diff one_ne_zero hx
  have hi := (hV.tangent j).diff one_ne_zero hx
  unfold row
  rw [pc_minus i (hi.mul he) (((hu.stripe j).tangent j).diff one_ne_zero hx), pc_mul i hi he,
    pc_comm i j (hu.stripe j x hx), hu.swap i j]
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply]
  ring
lemma Neumann.cross (hr : 0 ≤ r) (hu : Neumann r u) (hV : Regular r 2 V) (i j : ι) :
    bracket r V (row V i u) (row V j u) =
    size r V (pc j (pc i u)) ^ 2 + bracket r V (pc i (pc j V) * pc j u) (pc i u) := by
  have he : Regular r 1 V := hV.mono (by norm_num)
  have hv := hu.row1 hV j
  rw [hu.by_row hr he hv i,bracket_sym r V (pc i u),size_sq]
  let H := row V j (pc i u)
  have hT (x) (hx : x∈cube ι r) := hu.commute hV i j hx
  rw [show bracket r V (pc i (row V j u)) (pc i u) = bracket r V (H+pc i (pc j V)*pc j u) (pc i u) from
    (by unfold bracket; apply raw_congr; intro x hx; exact congr_arg (· * pc i u x) (hT x hx))]
  have hH : ContinuousOn H (cube ι r) :=
    ((hV.tangent j).cOn.mul (((hu.stripe i).tangent j).cOn)).sub (((hu.stripe i).tangent j).tangent_continuous j)
  rw [bracket_add hV.cOn hH (((hV.tangent j).tangent_continuous i).mul ((hu.stripe (n:=2) j).cOn)) ((hu.stripe (n:=2) i).cOn)]
  congr 1
  apply move_row hr he (hu.stripe i) (hu.stripe i)
  intro x hx h
  by_cases hh : j=i
  · subst j; rw [hu.normal i x hx h, mul_zero]
  rw [hu.mixed j i hh x hx h, zero_mul]

/-- Rough fixed-box gradient bounds without a gap, scrolling between V and 0. -/
lemma Neumann.rough (hr : 0 ≤ r) (hu : Neumann r u) (i : ι) :
    size r 0 (pc i u) ≤ (2*r) * size r 0 (pc i (pc i u)) := by
  let U := pc i u; let F := fun x : Points ι => x i
  have hU : Regular r 1 U := hu.stripe i
  have hF : Regular r 1 F := Regular.coordinate i
  have h := faces_zero hr ((hF.mul hU).mul hU) i (fun x hx h' => by simp [F, U, hu.normal i x hx h'])
  have hi : Regular r 1 (fun _ : Points ι => (0:ℝ)) := Regular.coefficient 0
  have hc : ContinuousOn (pc i U) (cube ι r) := hU.tangent_continuous i
  have he : EqOn (pc i (F*U*U)) ((U*U)+(2:ℝ) • ((F*U)*pc i U)) (cube ι r) := by
    intro x hx
    have hF' := hF.diff one_ne_zero hx
    have hU' := hU.diff one_ne_zero hx
    rw [pc_mul i (hF'.mul hU') hU', pc_mul i hF' hU', show pc i F x=1 from ?_]
    · simp only [Pi.smul_apply, Pi.mul_apply, Pi.add_apply, smul_eq_mul]; ring
    unfold pc F
    change fderiv ℝ (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => ℝ) i) x _=1; rw [ContinuousLinearMap.fderiv]; simp
  rw [← raw_none, raw_congr he, raw_add (V:=0) hi.cOn (hU.cOn.mul hU.cOn) (show ContinuousOn ((2:ℝ) • ((F*U)*pc i U)) (cube ι r) from continuousOn_const.smul ((hF.cOn.mul hU.cOn).mul hc)),raw_smul] at h
  have hg : size r 0 (F*U) ≤ r * size r 0 U := size_le_mul hi.cOn (hF.cOn.mul hU.cOn) hU.cOn hr fun x hx => by
    rw [Pi.mul_apply, abs_mul]; exact mul_le_mul_of_nonneg_right ((cube_iff hr).1 hx i) (abs_nonneg _)
  have hj := calc
    size r 0 U^2 = -2 * bracket r 0 (F*U) (pc i U) := by rw [size_sq]; unfold bracket; linarith only [h]
    _ ≤ 2 * size r 0 (F*U) * size r 0 (pc i U) := by
      have he := (abs_le.mp (cauchy (V:=0) hi.cOn (hF.cOn.mul hU.cOn) hc)).1
      linarith
    _ ≤ 2 * (r*size r 0 U) * size r 0 (pc i U) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg zero_le_two) (size_nn ..)
  change size r 0 U ≤ _*size r 0 (pc i U)
  rcases eq_or_lt_of_le (size_nn r 0 U) with hx|hx
  · rw [← hx]; exact mul_nonneg (mul_nonneg zero_le_two hr) (size_nn ..)
  apply le_of_mul_le_mul_left _ hx
  linarith only [hj]
end YM.Primitives.SmallFieldExterior
