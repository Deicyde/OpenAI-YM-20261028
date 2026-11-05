import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.QuadraticTilts
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Schur
import YM.Progress.STATIONARY_SCENES.Frames

/-!
# Selected covariance on counting, with all coordinates in ONE window system

E (6215–6555) estimate common to scalar normalization and Q ratio
letters even in sectors with rough V. The hypotheses `Lower`/Schur are
on the operated **precision**, retaining boundary rows even on a call to
a principal window. They have to be earned on the affine kernel! (Do
not supply here already the per-term costs on its log or ratio series.)

Width and expenditure post-L and post-direction orders, still before
actual Beta/output-volume/field/tags/wrapping instantiations. Covariance
inverse *upper* for the real Gaussian handled separately; both use the
same matrix. We use any windows including the addressed site, paying any
certified core radius, so applies on the actual torus with symmetric
endpoint convention too. Color multiplicity paid in `governs`. All finite
order V/smooth F interfaces distinct from Bond/Plaquette-Laurent claims.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Win
open Matrix Progress.StationaryScenes Finset Lattice MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius

structure Windows (n : Type*) where
  panel : n → Finset n
  owns (i : n) : i ∈ panel i

namespace Windows
variable {c : Side} {n : Type*} [Fintype n] [DecidableEq n] (P : Windows n)

/-- One column of one principal inverse. -/
def within (A : Matrix n n ℝ) : Matrix n n ℝ := Matrix.of fun i j =>
  if h : i∈P.panel j then ((A.submatrix ((↑):P.panel j→n) ((↑):P.panel j→n))⁻¹) ⟨i,h⟩ ⟨j,P.owns j⟩ else 0

def error (A : Matrix n n ℝ) : Matrix n n ℝ := A * P.within A - 1

/-- Lemma used also for Schur manipulations on covariance. -/
lemma stitch (A : Matrix n n ℝ) (hA : A.PosDef) : A⁻¹ * P.error A = P.within A - A⁻¹ := by
  rw [error,Matrix.mul_sub, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA.det_pos.ne'),
    Matrix.one_mul, Matrix.mul_one]

omit [Fintype n] in
private lemma subtype_identity (j : n) (i : P.panel j) :
    (1:Matrix (P.panel j) (P.panel j) ℝ) i ⟨j,P.owns j⟩ = (1 : Matrix n n ℝ) i j := by
  by_cases H : i.val=j <;> simp [Matrix.one_apply,Subtype.ext_iff,H]

lemma stitched (A : Matrix n n ℝ) (hA : A.PosDef) (i j : n) (hi : i∈P.panel j) :
    P.error A i j = 0 := by
  let Y := P.panel j
  let E := A.submatrix ((↑):Y→n) ((↑):Y→n)
  rw [error, Matrix.sub_apply, sub_eq_zero]
  calc
    _ = ∑ k ∈ Y, A i k * P.within A k j := by
      rw [Matrix.mul_apply]; symm; apply Finset.sum_subset (subset_univ _)
      intro m _ he
      change m∉P.panel j at he
      simp [within,he]
    _ = (E*E⁻¹) ⟨i,hi⟩ ⟨j,P.owns j⟩ := by
      rw [Matrix.mul_apply, ← Finset.sum_attach Y]
      refine Finset.sum_congr rfl fun x _ => ?_
      have he : x.val∈P.panel j := x.property
      simp only [within, Matrix.of_apply, dif_pos he]; rfl
    _ = _ := by rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hA.submatrix
                       (e:=((↑):Y→n)) (Subtype.val_injective)).det_pos.ne')]
                exact P.subtype_identity j ⟨_,hi⟩

/-- The selected covariance, *not* the inverse of an independently
restricted precision per letter. -/
def cov (A : Matrix n n ℝ) := (1/2 : ℝ) • (P.within A+(P.within A).transpose)

omit [Fintype n] in
lemma cov_hermitian (A : Matrix n n ℝ) : (P.cov A).IsHermitian := by
  unfold cov
  rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_add]
  change (1/2 : ℝ) • ((P.within A).transpose + P.within A) = _
  rw [add_comm]

/-- `S` in the density-ratio letters. -/
def untuned (A : Matrix n n ℝ) := A * P.cov A - 1

/-- Center (actual sector's affine source `b`). Extend inactive positions
by zero when requesting. -/
def center (A : Matrix n n ℝ) (b : n → ℝ) := -((P.within A).transpose *ᵥ b)



omit [Fintype n] in
lemma within_continuous {α : Type*} [TopologicalSpace α] {s : Set α} {f : α → Matrix n n ℝ}
    (h : ContinuousOn f s) (he : ∀ x∈s, (f x).PosDef) : ContinuousOn (fun x => P.within (f x)) s := by
  intro x hx
  apply continuousWithinAt_pi.mpr; intro i; apply continuousWithinAt_pi.mpr; intro j
  by_cases H : i∈P.panel j
  · let g (M : Matrix n n ℝ) := M.submatrix ((↑):P.panel j→n) ((↑):P.panel j→n)
    have hm : Continuous g := by
      refine continuous_matrix ?_; intro k l
      unfold g; fun_prop
    have hp := ResolventVolume.inv_continuous (hm.comp_continuousOn h) (fun y hy => ((he y hy).submatrix
        (e:=((↑):P.panel j→n)) Subtype.val_injective).det_pos.ne') x hx
    have hv := continuousWithinAt_pi.mp (continuousWithinAt_pi.mp hp ⟨i,H⟩) ⟨j,P.owns j⟩
    simp only [within,of_apply,H,dif_pos]
    exact hv
  simp only [within,of_apply,dif_neg H]; exact continuousWithinAt_const

omit [Fintype n] in
lemma cov_continuous {α : Type*} [TopologicalSpace α] {s : Set α} {f : α → Matrix n n ℝ}
    (h : ContinuousOn f s) (he : ∀ x∈s, (f x).PosDef) : ContinuousOn (fun x => P.cov (f x)) s := by
  have hP := within_continuous P h he
  unfold cov
  exact (continuousOn_const (c := (1/2:ℝ))).smul (hP.add ((show Continuous fun x : Matrix n n ℝ => x.transpose by fun_prop).comp_continuousOn hP))

section bounds
variable (d : n → Site c)

open Green

omit [Fintype n] [DecidableEq n] in
/-- Gap through window membership. -/
def Room (R : ℕ) := ∀ i j, separation (d i) (d j) ≤ R → i∈P.panel j

lemma inverse_price (A : Matrix n n ℝ) {η θ C r ν U : ℝ} (hη : 0<η) (hθ : 0<θ) (h : θ≤1)
    (hg : θ*C ≤ r/2) (hr : 0<r) (hν : ν < θ*η) (hp : governs d U) (hU : 0≤U)
    (hA : Both d d A η C C) (hh : A.IsHermitian) (hx : Bottom A r) :
    let Y := planePrice U (θ*η-ν)*(min 1 (r/2))⁻¹
    Both d d A⁻¹ ν Y Y ∧ Both d d (P.within A) ν Y Y := by
  intro Y
  have hk : 0 ≤ (min 1 (r/2))⁻¹ := inv_nonneg.mpr (le_min zero_le_one (half_pos hr).le)
  constructor
  · apply point_both hp hp hU hU hν hk
    intro i j
    simpa using (Green.inverse hη.le hr hθ.le h hg hh hx hA (0:ℝ) le_rfl).2.2 i j
  refine point_both hp hp hU hU hν hk fun i j => ?_
  by_cases he : i∈P.panel j
  · let q : P.panel j ↪ n := ⟨_, Subtype.val_injective (p:=fun i => i∈P.panel j)⟩
    have hi := Green.inverse (a:=d ∘ q) hη.le hr hθ.le h hg (hh.submatrix q) (hx.restrict q)
      ⟨hA.1.restrict _ q, hA.2.restrict _ q⟩ 0 le_rfl
    simpa [within,q,he] using hi.2.2 ⟨_,he⟩ ⟨_,P.owns j⟩
  simpa only [within,Matrix.of_apply,dif_neg he,abs_zero,mul_zero] using hk

/-- All price layers of one selected window. Here spend $\nu-\mu>
0$ on the error before enrolling small sums. Use even away from $t=1$ in
the determinant. -/
theorem window_price (A : Matrix n n ℝ) {η θ C r ν μ U : ℝ} (hη : 0<η) (hθ : 0<θ) (h : θ≤1)
    (hg : θ*C ≤ r/2) (hr : 0<r) (hν : ν < θ*η) (hp : governs d U) (hU : 0≤U)
    (hμ : 0 ≤ μ) (ht : μ < ν) (R : ℕ) (he : Room P d R) (hC : 0≤C)
    (hA : Both d d A η C C) (hh : A.IsHermitian) (hx : Bottom A r) :
    let Y := planePrice U (θ*η-ν)*(min 1 (r/2))⁻¹
    let s := Real.exp (-(ν-μ)*R)*(C*Y+1)
    Both d d A⁻¹ μ Y Y ∧ Both d d (P.within A) μ Y Y ∧
      Both d d (P.error A) μ s s ∧ Both d d (P.within A-A⁻¹) μ (Y*s) (Y*s) := by
  intro Y s
  obtain ⟨hz,hP⟩ := inverse_price P d A hη hθ h hg hr hν hp hU hA hh hx
  have hY : 0 ≤ Y := mul_nonneg (planePrice_nn hU (sub_pos.mpr hν))
    (inv_nonneg.mpr (le_min zero_le_one (half_pos hr).le))
  have hs : Both d d (P.error A) μ s s := by
    have hW : ν ≤ η := hν.le.trans (mul_le_of_le_one_left hη.le h)
    apply reduce_far (C:=C*Y+1) (D:=C*Y+1) _ ht.le R
    · intro i j h
      by_contra! h'
      exact h (P.stitched _ (Centered.symmetric_bottom hr hx hh) _ _ (he _ _ h'.le))
    rw [error, sub_eq_add_neg]
    exact plusBoth (timesBoth (hμ.trans ht.le) (monoBoth hA hW le_rfl le_rfl) hP hY hC) (negBoth (identities d _))
  have hI := monoBoth hz ht.le le_rfl le_rfl
  refine ⟨hI,monoBoth hP ht.le le_rfl le_rfl,hs,?_⟩
  rw [← P.stitch A (Centered.symmetric_bottom hr hx hh)]
  exact timesBoth hμ hI hs (by unfold s; positivity) hY

lemma covariance_price (A : Matrix n n ℝ) (hh : A.PosDef) {η Y ν C s : ℝ}
    (hA : Both d d A η C C) (hC : 0 ≤ C) (hν : 0≤ν) (hv : ν ≤ η)
    (hP : Both d d (P.within A) ν Y Y) (hs : 0 ≤ s)
    (hl : Both d d (P.within A-A⁻¹) ν s s) :
    Both d d (P.cov A) ν Y Y ∧ Both d d (P.cov A-A⁻¹) ν s s ∧
      Both d d (P.untuned A) ν (C*s) (C*s) := by
  have hs1 : Both d d (P.cov A) ν Y Y := by
    have hc := smulBoth (plusBoth hP (both_transpose hP)) (1/2)
    unfold cov; convert hc using 1 <;> norm_num <;> ring
  have hs2 : Both d d (P.cov A-A⁻¹) ν s s := by
    have ht : P.cov A-A⁻¹ = (1/2:ℝ) • ((P.within A-A⁻¹)+(P.within A-A⁻¹).transpose) := by
      rw [cov,Matrix.transpose_sub, show (A⁻¹).transpose = A⁻¹ from hh.inv.isHermitian]
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply,smul_eq_mul]; ring
    rw [ht]; convert smulBoth (plusBoth hl (both_transpose hl)) (1/2) using 1 <;> norm_num <;> ring
  refine ⟨hs1,hs2,?_⟩
  have ht : P.untuned A = A*(P.cov A-A⁻¹) := by
    rw [Matrix.mul_sub, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hh.det_pos.ne')]; rfl
  rw [ht]; exact timesBoth hν (monoBoth hA hv le_rfl le_rfl) hs2 hs hC

/-- Pay a bottom receipt for the *actual* approximation. -/
theorem covariance_floor (A : Matrix n n ℝ) (hh : A.PosDef) {η Y ν C s : ℝ}
    (hA : Both d d A η C C) (hC : 0<C) (hν : 0 ≤ ν) (hv : ν ≤ η)
    (hP : Both d d (P.cov A) ν Y Y) (hY : 0<Y)
    (hl : Both d d (P.cov A-A⁻¹) ν s s) (hs : s ≤ C⁻¹/2) :
    Bottom (P.cov A) (C⁻¹/2) ∧ Bottom (P.cov A)⁻¹ Y⁻¹ := by
  have hm : Bottom (P.cov A) (C⁻¹/2) := by
    intro v
    have hb := inverse_floor hA hC (hν.trans hv) hh v
    have he := abs_le.mp (to_schur hl hν v)
    rw [Matrix.sub_mulVec, dotProduct_sub] at he
    linarith [mul_le_mul_of_nonneg_right hs (Centered.dot_nonneg v)]
  exact ⟨hm,inverse_floor hP hY hν (Centered.symmetric_bottom (by positivity) hm (cov_hermitian P A))⟩
end bounds
end Windows
end YM.AnalyticNext.ConnectedActivity.Win
