import YM.Mink.Lorentz
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
Positive-rapidity convention. Cone via halfspace transport.
E eq:osconeM and . Shared with full-tube phase and analytic exchange.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Mink
open Set Filter Function Real
open scoped Topology Matrix.Norms.Frobenius InnerProductSpace BigOperators

abbrev Ray := {e : Space3 // ‖e‖ = 1}

namespace Ray
variable (e : Ray)

def along (x : E4) := inner ℝ (spatial x) e.val

def alongL : E4 →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
  { toFun := e.along
    map_add' _ _ := by simp [along,inner_add_left]
    map_smul' _ _ := by simp [along,real_inner_smul_left] }

def crossT : Coord := clockL.smulRight (position e.val 0) + e.alongL.smulRight (basis timeAxis)
def scalesT : Coord := clockL.smulRight (basis timeAxis) + e.alongL.smulRight (position e.val 0)

def shift (r : ℝ) : Coord := ContinuousLinearMap.id ℝ E4 + sinh r • e.crossT + (cosh r-1) • e.scalesT

@[simp] theorem alongL_at (x : E4) : e.alongL x = e.along x := rfl
lemma along_le (x : E4) : |e.along x| ≤ ‖spatial x‖ := by
  rw [along];simpa only [e.property, mul_one] using abs_real_inner_le_norm (spatial x) e.val

@[simp] theorem ticksT (x) : time (e.crossT x)=e.along x := by simp [crossT]
@[simp] theorem liesT (x) : spatial (e.crossT x)=time x • e.val := by simp [crossT]
@[simp] theorem ticksS (x) : time (e.scalesT x)=time x := by simp [scalesT]
@[simp] theorem liesS (x) : spatial (e.scalesT x)=e.along x • e.val := by simp [scalesT]

lemma newClock (r x) : time (e.shift r x)=cosh r*time x + sinh r*e.along x := by
  simp [shift];ring
lemma newSpace (r x) : spatial (e.shift r x)=spatial x+(sinh r*time x+(cosh r-1)*e.along x) • e.val := by
  simp [shift,add_smul,mul_smul,add_assoc]
lemma newProjection (r x) : e.along (e.shift r x)=sinh r*time x+cosh r*e.along x := by
  unfold along; rw [newSpace]; simp [along,inner_add_left, inner_smul_left,e.property]; ring

lemma adds (r s : ℝ) (x) : e.shift r (e.shift s x)=e.shift (r+s) x := by
  apply ext_by
  · simp_rw [newSpace,newClock,newProjection,add_assoc]; rw [← add_smul]; congr 2
    rw [sinh_add,cosh_add]; ring
  rw [newClock,newClock,newClock,newProjection,cosh_add,sinh_add];ring

@[simp] lemma beginShift : e.shift 0 = 1 := by ext1 x;simp [shift]

def motion (r : ℝ) : General where
  val := e.shift r
  inv := e.shift (-r)
  val_inv := by ext1 x; change e.shift r (e.shift (-r) x)=x; simp [adds]
  inv_val := by ext1 x; change e.shift (-r) (e.shift r x)=x; simp [adds]

@[simp] theorem steps (t x) : General.walk (e.motion t) x=e.shift t x := rfl
@[simp] theorem start : e.motion 0=1 := General.ext _ _ (by simp)
@[simp] theorem groupL (t r : ℝ) : e.motion (t+r)=e.motion t*e.motion r := General.ext _ _ (fun x => (adds e t r x).symm)
@[simp] theorem flip (t : ℝ) : (e.motion t)⁻¹ = e.motion (-t) := General.ext _ _ fun _ => rfl

lemma positive (t : ℝ) : General.stretch (e.motion t)=1 := by
  -- This boost is conjugate to its inverse and has positive determinant by dividing rapidity in two
  let D (t : ℝ) := General.stretch (e.motion t)
  have ht (r : ℝ) : D (t+r)=D t * D r := by simp [D]
  have hm : Lorentz.reverseL * e.motion t * Lorentz.reverseL⁻¹ = e.motion (-t) := by
    apply General.ext; intro x
    apply ext_by
    · simp [newSpace, along,add_smul,add_comm,add_left_comm, add_assoc]
    simp [newClock,along]
  have he : D t=D (-t) := by
    change General.stretch _ = General.stretch _; rw [← hm]
    have hp : General.stretch Lorentz.reverseL*General.stretch Lorentz.reverseL⁻¹ =1 := by rw [← General.comp,mul_inv_cancel,General.north]
    rw [General.comp,General.comp,mul_assoc,mul_left_comm, hp,mul_one]
  have hh := ht (-t); rw [add_neg_cancel, show D 0=1 by simp [D],← he] at hh
  have hn : D t = D (t/2)*D (t/2) := by
    unfold D; rw [← General.comp, ← groupL, add_halves]
  change D t=1
  nlinarith [sq_nonneg (D (t/2))]

lemma staysM (t : ℝ) (x : E4) : m (e.shift t x) = m x := by
  simp only [m,newClock,newSpace]
  rw [norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,e.property,mul_one,sq_abs]
  rw [show inner ℝ (spatial x) e.val=e.along x from rfl]
  linear_combination (time x^2-(e.along x)^2) * cosh_sq_sub_sinh_sq t

def boost (t : ℝ) : Lorentz := ⟨e.motion t,by
  have hm (t : ℝ) (x : E4) (h : x ∈ cone) : General.walk (e.motion t) x ∈ cone := by
    refine (cone_self _).mpr ⟨?_, e.staysM t x |>.symm ▸ ((cone_self _).mp h).2⟩
    have he : |sinh t|≤cosh t := le_of_sq_le_sq (by rw [sq_abs]; linarith [cosh_sq_sub_sinh_sq t]) (cosh_pos t).le
    have hh := (abs_le.mp (show |sinh t * e.along x| ≤ cosh t*time x from abs_mul .. |>.trans_le
      (mul_le_mul he ((e.along_le x).trans h) (abs_nonneg _) (cosh_pos t).le))).1
    rw [e.steps,newClock];linarith
  refine ⟨e.positive t, e.staysM t, fun x => ⟨fun h => ?_,hm t x⟩⟩
  have he := hm (-t) _ h
  rwa [← General.walk_mul,← e.groupL,neg_add_cancel,e.start,General.walk_one] at he⟩

@[simp] theorem boost_at (t x) : Lorentz.act (e.boost t) x=e.shift t x := rfl
@[simp] theorem boost_start : e.boost 0=1 := Subtype.ext e.start
@[simp] theorem boost_add (t r : ℝ) : e.boost (t+r)=e.boost t*e.boost r := Subtype.ext (e.groupL ..)
@[simp] theorem boost_neg (t : ℝ) : (e.boost t)⁻¹=e.boost (-t) := Subtype.ext (e.flip ..)

lemma continuousBoost : Continuous e.boost := by
  have he : Continuous e.motion := Units.continuous_iff.mpr
    ⟨show Continuous e.shift from by unfold shift;fun_prop,
      show Continuous (fun r => e.shift (-r)) from by unfold shift;fun_prop⟩
  exact Continuous.subtype_mk he _

theorem generator : HasDerivAt (fun t => Lorentz.act (e.boost t)) e.crossT 0 := by
  change HasDerivAt e.shift _ _
  simpa [shift,show (0:ℝ) • e.scalesT=0 by ext1; simp] using! ((hasDerivAt_const 0 (ContinuousLinearMap.id ℝ E4)).add ((hasDerivAt_sinh 0).smul_const
    e.crossT)).add (((hasDerivAt_cosh 0).sub_const 1).smul_const e.scalesT)

/-- Convenient positive coordinate ray. -/
def fromAxis (a : SpaceAxis) : Ray := ⟨EuclideanSpace.single a 1, by simp⟩
@[simp] theorem onAxis (a : SpaceAxis) (x) : along (fromAxis a) x=x a.castSucc := by
  rw [along]; dsimp only [fromAxis]; rw [EuclideanSpace.inner_single_right];simp [spatial]

@[simp] theorem time_gen (a : SpaceAxis) (x) : time ((fromAxis a).crossT x)=x a.castSucc := by simp

/-- Positive boost sign used in the boost Lie contract. -/
@[simp] theorem space_gen (a : SpaceAxis) (x : E4) (b : SpaceAxis) : spatial ((fromAxis a).crossT x) b =
    if b=a then x timeAxis else 0 := by
  by_cases h : b=a <;> simp [fromAxis,time, PiLp.single_apply, *,eq_comm]
end Ray

namespace Lorentz
/-- joint halfspace assertion for every Lorentz-transformed word
*really* sharpens to the cone (in the Euclidean frequency convention). -/
theorem from_half (x : E4) : x ∈ cone ↔ ∀ g : Lorentz, 0 ≤ time (act g.dual x) := by
  constructor
  · exact fun h g => ((cone_self _).mp ((keepsCone _ _).mpr h)).1
  intro H
  have he : 0 ≤ time x := by
    have h := H (dual (1 : Lorentz)); simpa only [dual_involution,act_one] using h
  change ‖spatial x‖ ≤ time x
  by_contra! h
  let T := ‖spatial x‖
  have hp : 0<T := he.trans_lt h
  let u : Ray := ⟨T⁻¹ • spatial x,by rw [norm_smul,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),inv_mul_cancel₀ hp.ne']⟩
  obtain ⟨s,hs,hw⟩ := exists_between (show time x/T<1 by rw [div_lt_iff₀ hp, one_mul];exact h)
  have hu : 0<s := (div_nonneg he hp.le).trans_lt hs
  let t := artanh s
  have hv : sinh t = s * cosh t := by
    apply (div_eq_iff (cosh_pos _).ne').mp; rw [← tanh_eq_sinh_div_cosh]; exact tanh_artanh ⟨by linarith,hw⟩
  have hA := H (dual (u.boost (-t)))
  rw [dual_involution,Ray.boost_at,Ray.newClock, sinh_neg, cosh_neg,hv] at hA
  have hb : u.along x=T := by
    simp only [u,Ray.along, real_inner_smul_right,real_inner_self_eq_norm_sq, pow_two]
    change T⁻¹ * (T*T) = T; field_simp
  rw [hb] at hA
  have hh := (mul_lt_mul_of_pos_left ((div_lt_iff₀ hp).mp hs) (cosh_pos t))
  linarith

end Lorentz
end YM.Mink
