import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.MAXWELL.Scripts
import YM.Pressure.Seeds
import YM.Work.A16



/-!
# Continuing the tensor matrices to the actual Lorentz group

Time sign fixed by `plane timeAxis i.castSucc` and the convention in
Ray.shift. Only propagate entire identities, one boost at a time;
no path-connectedness shortcut for a higher dimensional zero set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Analysis Complex Mink
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

/-- Entry-wise Wick rotation embedding. -/
def lamp (a : Axis) : ℂ := if a=timeAxis then -I else 1

def stencil (L : Lorentz) : Ink :=
    fun a b => lamp a * (Lorentz.act L (basis b) a : ℂ) * (lamp b)⁻¹

@[simp] lemma lamp_nz (a) : lamp a≠0 := by unfold lamp; split_ifs <;> simp

lemma stencil_cont : Continuous stencil := by
  apply continuous_pi; intro a; apply continuous_pi; intro b
  let f : Lorentz → E4 := fun L => Lorentz.act L (basis b)
  have h : Continuous f := Lorentz.usual.clm_apply continuous_const
  exact (continuous_const.mul (continuous_ofReal.comp ((EuclideanSpace.proj (𝕜:=ℝ) a).continuous.comp h))).mul continuous_const

def follow (A B : Ink) : Ink := fun i j => ∑ k, A i k*B k j

lemma follow_left (A : Ink) : ContDiff ℂ ω (fun B => follow A B) := by
  unfold follow; apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j
  apply ContDiff.sum; intro k _; fun_prop
lemma follow_right (B : Ink) : ContDiff ℂ ω (fun A => follow A B) := by
  unfold follow; apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j
  apply ContDiff.sum; intro k _; fun_prop

lemma stencil_one : stencil 1=paints 1 := by
  funext i j
  change lamp i * _ * (lamp j)⁻¹ = ((1:M4) i j:ℂ)
  by_cases h : i=j
  · subst j; simp
  simp [h]

lemma stencil_mul (L P : Lorentz) : stencil (L*P)=follow (stencil L) (stencil P) := by
  funext i j
  unfold stencil follow
  rw [Lorentz.act_mul]
  have he : Lorentz.act L (Lorentz.act P (basis j)) i = ∑ k : Axis, (Lorentz.act P (basis j)) k * (Lorentz.act L (basis k)) i := by
    conv_lhs => rw [show Lorentz.act P (basis j) = ∑ k : Axis, Lorentz.act P (basis j) k • basis k by
      ext1 k; simp]
    rw [map_sum]; simp
  simp_rw [he, Complex.ofReal_sum,Complex.ofReal_mul,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl; intro k _; field_simp


lemma follows (A B : Ortho) : follow (paints A) (paints B)=paints (A*B) := by
  ext i j; simp only [follow, paints, ← Complex.ofReal_mul,← Complex.ofReal_sum]; rfl

lemma spatial_axis (s : Ortho) (h : Lorentz.spatialTurn s) : s.move (basis timeAxis)=basis timeAxis := by
  apply eq_of_sub_eq_zero
  let y := s.motion (basis timeAxis)
  have ht : ⟪basis timeAxis,y⟫_ℝ = 1 := by rw [basis_inner]; exact (h.2 (basis timeAxis)).trans (by simp [time])
  have he : ‖y‖ = 1 := by exact (s.motion.norm_map _).trans (basis_norm _)
  have hm : ‖basis timeAxis-y‖^2 = 0 := by rw [norm_sub_sq_real]; simp [he,ht]; ring
  have hf : basis timeAxis=y := sub_eq_zero.mp (by simpa using hm)
  exact sub_eq_zero.mpr hf.symm

lemma photos (s : Ortho) (h : Lorentz.spatialTurn s) : stencil (Lorentz.room s h)=paints s := by
  funext i j; change lamp i*(s.move (basis j) i : ℂ)*(lamp j)⁻¹ = _
  have he (i j) : stencil (Lorentz.room s h) i j = lamp i*(s.val i j:ℂ)*(lamp j)⁻¹ := by
    change lamp i*(s.move (basis j) i : ℂ)*(lamp j)⁻¹ = _; rw [Ortho.move,M4.move_basis]
  change _ = (s.val i j:ℂ)
  rw [← M4.move_basis s.val i j]
  change _ = (s.move (basis j) i:ℂ)
  by_cases hx : j=timeAxis
  · subst j; rw [spatial_axis s h]; by_cases ht : i=timeAxis
    · subst i; simp
    simp [basis_eq,ht]
  by_cases hu : i=timeAxis
  · subst i; have ht : (s.move (basis j)) timeAxis = 0 := (h.2 (basis j)).trans (by simp [time,Ne.symm hx])
    simp [ht]
  simp [lamp,hx,hu]

lemma fixed_inverse {L : Lorentz} (h : Lorentz.act L (basis timeAxis) = basis timeAxis) :
    Lorentz.act L⁻¹ (basis timeAxis)=basis timeAxis := by nth_rw 1 [← h]; exact Lorentz.starts ..

/-- Cos/sin in the indicated rows. -/
def stroll (a : SpaceAxis) (z : ℂ) : Ink := fun i k =>
    if i=timeAxis then cos z * (kr timeAxis k:ℂ) + sin z * (kr a.castSucc k:ℂ)
    else if i=a.castSucc then cos z * (kr a.castSucc k:ℂ) - sin z * (kr timeAxis k:ℂ)
    else (kr i k:ℂ)

lemma stroll_diff (a : SpaceAxis) : ContDiff ℂ ω (stroll a) := by
  apply contDiff_pi.mpr; intro i; apply contDiff_pi.mpr; intro j
  by_cases h : i=timeAxis
  · simp only [stroll,h, if_true]; fun_prop
  by_cases hv : i=a.castSucc
  · simp only [stroll,hv,show a.castSucc ≠ timeAxis from Fin.castSucc_ne_last _, if_false, if_true]; fun_prop
  simp only [stroll,h,hv,if_false]; exact contDiff_const

lemma writes_axes (a : SpaceAxis) (r : ℝ) : paints (Ortho.oneParameter (Ortho.plane timeAxis a.castSucc) r) = stroll a r := by
  have hh : timeAxis ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last _)
  let U := Ortho.oneParameter (Ortho.plane timeAxis a.castSucc) r
  funext i k
  obtain ⟨hf,hg,ht⟩ := Work.A13.plane_givens hh (basis k) r
  rw [paints, ← M4.move_basis (Ortho.oneParameter _ _).val i k]; change (U.move (basis k) i:ℂ) = _
  unfold stroll; split_ifs with h h
  · subst i; rw [show U.move (basis k) _ = _ from hf]; push_cast; rfl
  · subst i; rw [show U.move (basis k) _ = _ from hg]; push_cast; rfl
  rw [show U.move (basis k) i = _ from ht i (by assumption) (by assumption)]; rfl

lemma night (a : SpaceAxis) (t : ℝ) : stencil ((Ray.fromAxis a).boost t)=stroll a ((t:ℂ)*(-I)) := by
  let U := Ray.fromAxis a
  have ht (b k : Axis) (hb : b ≠ timeAxis) (hd : b ≠ a.castSucc) : U.shift t (basis k) b = basis k b := by
    obtain ⟨i,rfl⟩ : ∃ i : SpaceAxis, i.castSucc=b := ⟨_, Fin.castSucc_castPred b hb⟩
    exact (Work.A16.boost_keeps_other a i (fun h => hd (congr_arg Fin.castSucc h)) t (basis k))

  have hi (x : ℝ) : Complex.cos ((x:ℂ)*(-I))=(Real.cosh x:ℂ) := by simp [Complex.cos_mul_I]
  have hj (x : ℝ) : Complex.sin ((x:ℂ)*(-I))= -I * (Real.sinh x:ℂ) := by simp [Complex.sin_mul_I, mul_comm Complex.I]
  funext i k
  unfold stencil; rw [Ray.boost_at]; change lamp i * (U.shift t (basis k) i:ℂ) * (lamp k)⁻¹ = _
  unfold stroll; rw [hi,hj]
  have he : timeAxis ≠ a.castSucc := Ne.symm (Fin.castSucc_ne_last a)
  split_ifs with h h
  · subst i
    rw [show (U.shift t (basis k)) timeAxis = _ from U.newClock t (basis k)]
    by_cases hk : k=timeAxis
    · subst k; simp [lamp, kr, time,Ray.onAxis,U,Ne.symm he, mul_comm Complex.I, mul_assoc]
    · simp [lamp, kr, time, Ray.onAxis,U,Ne.symm hk,hk]; split_ifs <;> simp
  · subst i
    rw [← Ray.onAxis a (U.shift t (basis k)), show _ = _ from U.newProjection t (basis k)]
    by_cases hk : k=timeAxis
    · subst k; simp [lamp, kr,time,Ray.onAxis,U,Ne.symm he]; ring
    · simp [lamp,kr,time,Ray.onAxis,U,hk,Ne.symm hk,Ne.symm he]; split_ifs <;> simp
  rw [ht i k (by assumption) (by assumption)]
  by_cases H : k=i
  · subst k; simp [kr]
  simp [kr,Ne.symm H]

end YM.Maxwell.Free
