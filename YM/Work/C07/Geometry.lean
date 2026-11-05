import YM.Bid.Corners

/-!
# Single-parameter paths for the boost identity

`scaledTimes z`: z multiplies all the *real* times of the integration variables. The
imaginary-offset term i*y is untouched. At `z=1` these are the ordered complex times used
in psi. At `z=i*w` the times are again purely imaginary, with height y' = y+w*t. Use the
position map `foldE` which puts in y' as the Euclidean time. A good vector field `orbit`
on the original integration variables maps under `foldE` to w times the Euclidean rotation
generator at `foldE`. This avoids dividing by w, and can be used to get spatial as well as
temporal derivatives on tests, *before* doing analytic continuation. It does not require F
to have pointwise spatial derivatives at strict times off the Euclidean slice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C07
open Boundary Mink Set Filter Function Analysis Complex Bid
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

def scaledTimes (y : Heights n) (z : ℂ) (p : Points n) : Times n :=
  fun i => z * ↑(time (p i)) + (↑(y i) : ℂ)*I

lemma scaled_one (y : Heights n) (p : Points n) : scaledTimes y 1 p = shift p y := by
  ext1 i; simp [scaledTimes, shift]

def stretchY (y : Heights n) (w : ℝ) (p : Points n) : Heights n :=
  fun i => y i + w * time (p i)

lemma scaled_imag (y : Heights n) (w : ℝ) (p : Points n) :
    scaledTimes y ((w : ℂ)*I) p = fun i => (stretchY y w p i : ℂ)*I := by
  ext1 i
  simp [scaledTimes, stretchY]
  ring

lemma scaled_strict_imag (y : Heights n) (w : ℝ) (p : Points n) :
    scaledTimes y ((w : ℂ)*I) p ∈ strict n ↔ stretchY y w p ∈ east n := by
  rw [scaled_imag]; simp [strict]

def foldE (y : Heights n) (w : ℝ) (p : Points n) : Points n :=
  place (trace p) (stretchY y w p)

/-- Linear part of the fold. -/
def foldL (w : ℝ) : Points n →L[ℝ] Points n := LinearMap.toContinuousLinearMap
  { toFun := foldE 0 w
    map_add' := fun p q => PiLp.ext fun i => by
      apply ext_by
      · simp [foldE, trace, place]
      simp [foldE, trace, place, stretchY, mul_add]
    map_smul' := fun c p => PiLp.ext fun i => by
      apply ext_by
      · simp [foldE, trace, place]
      simp [foldE, trace, place, stretchY, mul_left_comm] }

private lemma fold_eq (y : Heights n) (w : ℝ) (p : Points n) :
    foldE y w p = dawn y + foldL w p := by
  change _ = dawn y + foldE 0 w p
  exact PiLp.ext fun i => by apply ext_by <;> simp [foldE, dawn, place, trace, stretchY]

lemma fold_smooth (y : Heights n) (w : ℝ) : ContDiff ℝ ∞ (foldE y w) := by
  rw [funext (fold_eq y w)]
  exact contDiff_const.add (foldL w).contDiff

lemma fold_derivative (y : Heights n) (w : ℝ) (p : Points n) :
    HasFDerivAt (foldE y w) (foldL w) p := by
  rw [funext (fold_eq y w)]
  exact (foldL w).hasFDerivAt.const_add _

def orbit (a : SpaceAxis) (y : Heights n) (w : ℝ) (p : Points n) :=
    ∑ i : Fin n, (p i a.castSucc • Points.direction i timeAxis -
      (w * stretchY y w p i) • Points.direction i a.castSucc)

private lemma turnsPoint (p : E4) (a b : Axis) (hab : a ≠ b) :
    M4.move (Ortho.plane a b).val p = p b • basis a - p a • basis b := by
  apply PiLp.ext
  intro i
  rw [M4.at_coord]
  rcases eq_or_ne i a with rfl | hi
  · simp [Ortho.plane, Matrix.single_apply, hab, Ne.symm hab]
  rcases eq_or_ne i b with rfl | hJ
  · simp [Ortho.plane, Matrix.single_apply, hab, Ne.symm hab]
  simp [Ortho.plane, hi, hJ, Ne.symm hi, Ne.symm hJ]

private lemma orbit_coord (a : SpaceAxis) (y : Heights n) (w : ℝ) (p : Points n) (i : Fin n) :
    orbit a y w p i = p i a.castSucc • basis timeAxis - (w * stretchY y w p i) • basis a.castSucc := by
  let Q : Points n →L[ℝ] E4 := PiLp.proj 2 (fun _ => E4) i
  change Q _ = _
  unfold orbit
  rw [map_sum, Finset.sum_eq_single i]
  · change (_ - _ : Points n) i = _
    simp [Points.direction]
  · intro j _ h
    change (_ - _ : Points n) i = _
    simp [Points.direction, Ne.symm h]
  · simp

lemma orbit_image (a : SpaceAxis) (y : Heights n) (w : ℝ) (p : Points n) :
    foldL w (orbit a y w p) = w • points fun i =>
      M4.move (Ortho.plane timeAxis a.castSucc).val (foldE y w p i) := by
  change foldE _ _ _ = _
  apply PiLp.ext
  intro i
  have h : a.castSucc ≠ timeAxis := Fin.castSucc_ne_last _
  have hA : foldE y w p i a.castSucc = p i a.castSucc := by simp [foldE, place, trace, spatial, position]
  have hB : foldE y w p i timeAxis = stretchY y w p i := time_position ..
  simp only [turnsPoint _ _ _ h.symm, points_apply, hA, hB, PiLp.smul_apply]
  apply ext_by
  · simp [foldE, place, trace, orbit_coord, sub_eq_add_neg, mul_smul]
  · simp [foldE, place, stretchY, orbit_coord, sub_eq_add_neg, h.symm, time]
    exact time_position ..

/-- Differential tested on the spacetime variables, z=i*w case is D along the orbit,
z=1 is exactly the test function in the goal. -/
def testField (a : SpaceAxis) (y : Heights n) (z : ℂ) (f : Joint n) (p : Points n) :=
    ∑ i : Fin n, ((p i a.castSucc : ℂ) * realTerm i timeAxis f p +
      z * scaledTimes y z p i * realTerm i a.castSucc f p)

lemma test_one (a : SpaceAxis) (y : Heights n) (f : Joint n) (p : Points n) :
    testField a y 1 f p = inclined a y f p := by
  rw [testField, inclined, _root_.sum_apply]
  apply Finset.sum_congr rfl; intro i _
  simp [multiplier_test, scaled_one, shift, time, add_mul, add_assoc]

lemma test_imag (a : SpaceAxis) (y : Heights n) (w : ℝ) (f : Joint n) (p : Points n) :
    testField a y ((w : ℂ)*I) f p = fderiv ℝ f p (orbit a y w p) := by
  rw [testField, orbit, map_sum]; apply Finset.sum_congr rfl; intro i _
  rw [map_sub, map_smul, map_smul]
  simp only [scaled_imag, realTerm, SchwartzMap.lineDerivOp_apply_eq_fderiv, real_smul,
    ofReal_mul]
  have he (u v : ℂ) : u*I*(v*I) = -(u*v) := by rw [mul_mul_mul_comm, I_mul_I]; ring
  rw [he]
  ring

lemma test_zero_off (a : SpaceAxis) (y : Heights n) (z : ℂ) (f : Joint n) {p : Points n}
    (h : p ∉ tsupport f) : testField a y z f p = 0 := by
  have hh (i : Fin n) (b : Axis) : realTerm i b f p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun H => h (SchwartzMap.tsupport_lineDerivOp_subset _ _ H))
  simp [testField, hh]

end YM.Work.C07
