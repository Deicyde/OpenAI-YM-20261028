import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.A13
import YM.Work.B06

/-!
# Coordinates for a *direct* Lorentz descendant for RLights / RStage

Instead of shipping a descended action as an additional compatibility hypothesis,
we'll produce one from the given action on Euclidean fields. (In particular this
route will not use changes of basis with Maxwell fields or require a descendant
of some other action.) Here are the real coordinates used in the proof. We keep
math on matrices rather than assuming Lie group integration. Time last, Θ is
*time* reflection. A positive-rapidity boost has generator plane(0,l) Θ (0 here
meaning **time**) in these coordinates; continue the Euclidean **label** action
with generator -i Σ(0,l).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Function Filter Set Mink
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace

def coords : Coord →L[ℝ] M4 := LinearMap.toContinuousLinearMap {
  toFun e := (Matrix.toEuclideanLin (n:=Axis) (m:=Axis) (𝕜:=ℝ)).symm e.toLinearMap
  map_add' _ _ := by rw [ContinuousLinearMap.toLinearMap_add, map_add]
  map_smul' _ _ := by rw [ContinuousLinearMap.toLinearMap_smul, map_smul]; rfl }

lemma coords_move (p : Coord) (x : E4) : M4.move (coords p) x = p x := by
  unfold M4.move coords
  change Matrix.toEuclideanLin (Matrix.toEuclideanLin.symm p.toLinearMap) x = p x
  rw [LinearEquiv.apply_symm_apply]; rfl

lemma entry (p : Coord) (i j : Axis) : coords p i j = p (basis j) i := by
  rw [← M4.move_basis (coords p), coords_move]

lemma coords_mul (e f : Coord) : coords (e*f)=coords e * coords f := by
  ext i j
  rw [entry, ← M4.move_basis (coords e * coords f), M4.move_mul]
  simp only [coords_move]; rfl

lemma coords_star (p : Coord) : coords p.adjoint = star (coords p) := by
  ext i j
  rw [entry, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, entry]
  rw [star_trivial, ← basis_inner, ← basis_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, real_inner_comm]

def mat (g : Lorentz) := coords (Lorentz.act g)

lemma mat_one : mat 1=1 := by
  ext i j; simp [mat, entry, Matrix.one_apply]

lemma mat_mul (g h : Lorentz) : mat (g*h)=mat g * mat h := coords_mul g.act h.act

lemma mat_inv_mul (g : Lorentz) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
lemma mat_mul_inv (g : Lorentz) : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]

lemma mat_continuous : Continuous mat := coords.continuous.comp Lorentz.usual

lemma mat_room (k : Ortho) (h : Lorentz.spatialTurn k) : mat (.room k h) = k.val := by
  ext i j
  change coords _ i j = _
  rw [entry]
  change M4.move k.val (basis j) i = k.val i j
  simp

/-- Θ for spacetime signature; NOT reversal of the spatial axes. -/
def theta : M4 := (Signed.reflect timeAxis).val

lemma theta_entry (i j : Axis) : theta i j = if i=timeAxis then -basis j i else basis j i := by
  rw [← M4.move_basis theta]; exact Signed.mirrored timeAxis i _

lemma star_theta : star theta = theta := by
  ext i j
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, theta_entry, theta_entry]
  by_cases h : i=j
  · subst i; exact star_trivial _
  simp [basis_eq,h,Ne.symm h]

lemma theta_sq : theta * theta=1 := by
  have he : star theta * theta=1 := (Signed.reflect _).property.1
  rwa [star_theta] at he

lemma reverse_time_sign : coords Lorentz.reverseL.val = -theta := by
  ext i j
  rw [entry]; change General.walk Lorentz.reverseL (basis j) i = _
  rw [Lorentz.reversing]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨a, rfl⟩ | rfl
  · change spatial (position _ _) a = - theta a.castSucc j
    rw [spatial_position, theta_entry, if_neg (Fin.castSucc_ne_last _)]
    rfl
  change time (position _ _) = - theta timeAxis j
  rw [time_position, theta_entry, if_pos rfl, neg_neg]; rfl

lemma mat_dual (g : Lorentz) : mat g.dual=theta * mat g * theta := by
  change coords (Lorentz.reverseL.val * g.val.val * Lorentz.reverseL.val) = _
  rw [coords_mul, coords_mul, reverse_time_sign, neg_mul, neg_mul_neg]; rfl

lemma mat_star (g : Lorentz) : star (mat g)=theta * mat g⁻¹ * theta := by
  rw [← mat_dual]
  simp only [mat, Lorentz.dual_adjoint, inv_inv, coords_star]

/-- Euclidean time-plane generator corresponding to this choice of boost. -/
abbrev Q (a : SpaceAxis) := Ortho.plane timeAxis a.castSucc

def B (a : SpaceAxis) := coords (Ray.fromAxis a).crossT

lemma theta_left (A : M4) (i j : Axis) : (theta*A) i j = if i=timeAxis then -A i j else A i j := by
  rw [← M4.move_basis (theta*A), M4.move_mul]; change Ortho.move (Signed.reflect timeAxis) (M4.move A (basis j)) i = _
  simp

lemma theta_right (A : M4) (i j : Axis) : (A*theta) i j = if j=timeAxis then -A i j else A i j := by
  have ht := theta_left (star A) j i
  rw [← star_theta, ← star_mul] at ht
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial] using ht

lemma B_time (a : SpaceAxis) (j : Axis) : B a timeAxis j=basis j a.castSucc := by
  rw [B, entry]; exact Ray.time_gen a _

lemma B_space (a : SpaceAxis) (i : SpaceAxis) (j : Axis) :
    B a i.castSucc j= if i=a then basis j timeAxis else 0 := by
  rw [B, entry]; exact Ray.space_gen a _ i

lemma BQ (a : SpaceAxis) : B a * theta = (Q a).val := by
  ext i j
  rw [theta_right, ← M4.move_basis (Q a).val i j,
    Work.A13.plane_field_apply (Fin.castSucc_ne_last a).symm]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨l, rfl⟩ | rfl
  · rw [B_space]
    by_cases hj : j=timeAxis
    · subst j; by_cases h : l=a <;> simp only [timeAxis, Fin.castSucc_ne_last,
        Fin.castSucc_inj, h, ↓reduceIte, basis_eq, neg_zero]
    rw [if_neg (Fin.castSucc_ne_last _)]  -- RHS plane test
    simp only [Fin.castSucc_inj, if_neg hj, basis_eq, timeAxis] at *
    simp only [if_neg (Ne.symm hj), neg_zero, ite_self]
  rw [B_time, if_pos rfl]  -- RHS plane test
  by_cases hj : j=timeAxis
  · subst j; simp
  rw [if_neg hj]

lemma time_parity (a : SpaceAxis) : theta * B a = -(B a * theta) := by
  ext i j
  rw [theta_left, Matrix.neg_apply, theta_right]
  rcases Fin.eq_castSucc_or_eq_last i with ⟨l, rfl⟩ | rfl
  · rw [B_space, if_neg (Fin.castSucc_ne_last _)]
    by_cases hj : j=timeAxis
    · rw [if_pos hj, neg_neg]
    rw [if_neg hj, basis_eq, if_neg (Ne.symm hj)]; simp
  rw [B_time, if_pos rfl]
  by_cases hj : j=timeAxis
  · subst j; simp
  rw [if_neg hj]

lemma B_star (a : SpaceAxis) : star (B a)=B a := by
  have he : star (B a * theta) = -(B a * theta) := by rw [BQ]; exact (Q a).2
  rw [star_mul, star_theta, ← time_parity] at he
  have hh := congr_arg (theta * ·) he
  simpa only [← mul_assoc, theta_sq, one_mul] using hh

abbrev boost (a : SpaceAxis) (p : ℝ) : Lorentz := (Ray.fromAxis a).boost p

lemma mat_boost (i : SpaceAxis) : HasDerivAt (fun t => mat (boost i t)) (B i) 0 :=
  coords.hasFDerivAt.comp_hasDerivAt 0 (Ray.generator (Ray.fromAxis i))

lemma at_boost (i : SpaceAxis) (s : ℝ) : HasDerivAt (fun t => mat (boost i t))
    (mat (boost i s)*B i) s := by
  have he := ((mat_boost i).const_mul (mat (boost i s))).scomp_of_eq s
    ((hasDerivAt_id' s).sub_const s) (by simp)
  simpa only [comp_def, one_smul, ← mat_mul, boost, ← Ray.boost_add, add_sub_cancel] using! he

lemma at_boost' (i : SpaceAxis) (s : ℝ) : HasDerivAt (fun t => mat (boost i t))
    (B i * mat (boost i s)) s := by
  have he := ((mat_boost i).mul_const (mat (boost i s))).scomp_of_eq s
    ((hasDerivAt_id' s).sub_const s) (by simp)
  simpa only [comp_def, one_smul, ← mat_mul, boost, ← Ray.boost_add, sub_add_cancel] using! he

lemma room_mat_inv (k : Ortho) (h : Lorentz.spatialTurn k) : mat (Lorentz.room k h)⁻¹ = star k.val := by
  -- use common inverse
  let g := Lorentz.room k h
  have hm : k.val*mat g⁻¹=1 := mat_room k h ▸ mat_mul_inv g
  calc
    _ = (star k.val * k.val) * mat g⁻¹ := by rw [k.property.1, one_mul]
    _ = _ := by rw [mul_assoc,hm,mul_one]

lemma room_time_fixed (k : Ortho) (h : Lorentz.spatialTurn k) :
    (Lorentz.room k h).act (basis timeAxis)=basis timeAxis := by
  change k.move (basis timeAxis) = _
  apply ext_by _ (h.2 _)
  have he := squares (k.move (basis timeAxis))
  rw [Ortho.move_norm, h.2, roll_clock, basis_norm] at he
  rw [roll_space]; apply norm_eq_zero.mp
  nlinarith

lemma space_parity (k : Ortho) (h : Lorentz.spatialTurn k) : theta * k.val = k.val * theta := by
  have he := mat_star (Lorentz.room k h)⁻¹
  rw [room_mat_inv, star_star, inv_inv, mat_room] at he
  calc theta*k.val = theta*(theta*k.val*theta) := congr_arg _ he
       _ = k.val*theta := by rw [← mul_assoc, ← mul_assoc, theta_sq, one_mul]

end YM.Next.BOUNDARY.Descent
