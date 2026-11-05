import YM.Next.BOUNDARY.Coordinates
import YM.Work.A16

/-!
# A decomposition differentiable along matrix paths into axis boosts and spatial rotation

We use this instead of an arbitrary choice of product given by generation.
It is global, including at elements which are spatial rotations, and right-equivariant
with respect to the spatial stabilizer. All the differential lemmas needed are
stated along ordinary differentiable paths of *matrices*, not using a manifold
structure on the subgroup. Elimination order is 0,1,2 in the 3 *space* axes.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Function Filter Set Mink Real
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius

def speed (i : SpaceAxis) (g : Lorentz) := mat g i.castSucc timeAxis/mat g timeAxis timeAxis

def rapidity (i : SpaceAxis) (g : Lorentz) := artanh (speed i g)

def reduce (i : SpaceAxis) (g : Lorentz) := boost i (-(rapidity i g)) * g

private lemma duration_positive (g : Lorentz) : 0 < mat g timeAxis timeAxis := by
  have he : basis timeAxis ∈ inside := by
    change ‖spatial (basis timeAxis)‖ < time _
    simp
  rw [mat, entry]; exact ((strict_self _).1 ((g.stays _).mpr he)).1

private lemma speed_inside (i : SpaceAxis) (g : Lorentz) : speed i g ∈ Ioo (-1 : ℝ) 1 := by
  have he : basis timeAxis ∈ inside := by
    change ‖spatial (basis timeAxis)‖ < time _; simp
  let x := g.act (basis timeAxis)
  have hh : x∈inside := (g.stays _).mpr he
  have hm := (duration_positive g)
  have hk : |x i.castSucc| < time x := by
    rw [← Ray.onAxis]; exact ((Ray.fromAxis i).along_le x).trans_lt hh
  have hf : mat g i.castSucc timeAxis = x i.castSucc := entry ..
  have ht : mat g timeAxis timeAxis=time x := entry ..
  rw [speed,hf,ht]; rw [ht] at hm
  rw [abs_lt] at hk
  exact ⟨(lt_div_iff₀ hm).mpr (by linarith [hk.1]), (div_lt_iff₀ hm).mpr (by linarith [hk.2])⟩

lemma reduces (i : SpaceAxis) (g : Lorentz) : spatial ((reduce i g).act (basis timeAxis)) i=0 := by
  let e := Ray.fromAxis i
  let x := g.act (basis timeAxis)
  let r := rapidity i g
  have hT := duration_positive g
  rw [mat, entry] at hT
  have hr : sinh r/cosh r = e.along x/time x := by
    rw [← tanh_eq_sinh_div_cosh]; exact (Real.tanh_artanh (speed_inside i g)).trans (by
      unfold speed; simp only [e, Ray.onAxis,x,mat,entry]; rfl)
  have hh := (div_eq_div_iff (cosh_pos _).ne' (show time x ≠ 0 from hT.ne')).mp hr
  change ((e.shift (-r) x) i.castSucc) = 0
  rw [← Ray.onAxis]
  change e.along (e.shift (-r) x)=0
  rw [Ray.newProjection, sinh_neg, cosh_neg]; linarith

lemma undo_reduce (i : SpaceAxis) (g : Lorentz) : boost i (rapidity i g) * reduce i g = g := by
  rw [reduce, ← mul_assoc, boost, boost, ← Ray.boost_add]
  simp

lemma keep_reduce (i j : SpaceAxis) (h : j≠i) (g : Lorentz) :
    spatial ((reduce i g).act (basis timeAxis)) j = spatial (g.act (basis timeAxis)) j := by
  rw [reduce,Lorentz.act_mul,boost, Ray.boost_at]
  exact Work.A16.boost_keeps_other i j h _ _

-- names for the parameters; reduction order explicit

def b0 (g : Lorentz) := rapidity 0 g
def b1 (g : Lorentz) := rapidity 1 (reduce 0 g)
def b2 (g : Lorentz) := rapidity 2 (reduce 1 (reduce 0 g))

def restG (g : Lorentz) := reduce 2 (reduce 1 (reduce 0 g))

lemma fixes_time (g : Lorentz) : (restG g).act (basis timeAxis)=basis timeAxis := by
  have he : spatial ((restG g).act (basis timeAxis))=0 := by
    apply PiLp.ext; intro i
    change spatial ((restG g).act (basis timeAxis)) i = 0
    fin_cases i
    · rw [restG, keep_reduce _ _ (by decide),keep_reduce _ _ (by decide)]; exact reduces 0 g
    · rw [restG, keep_reduce _ _ (by decide)]; exact reduces _ _
    exact reduces _ _
  apply ext_by
  · simpa using he
  have ht := (restG g).keeps (basis timeAxis)
  simp only [m, he, roll_clock, roll_space,norm_zero] at ht
  have hh := duration_positive (restG g)
  rw [mat, entry] at hh
  have hp : 0 < time ((restG g).act (basis timeAxis)) := hh
  rw [roll_clock]; nlinarith

/-- Choice here is of the spatial Lorentz element read as Ortho. The output is
unique, by the `mat` readout. -/
def orientation (g : Lorentz) : Ortho :=
  (Work.A16.exists_room_of_fix (restG g) (fixes_time g)).choose

lemma oriented (g : Lorentz) : Lorentz.spatialTurn (orientation g) :=
  (Work.A16.exists_room_of_fix (restG g) (fixes_time g)).choose_spec.choose

lemma read_out (g : Lorentz) : Lorentz.room (orientation g) (oriented g)=restG g :=
  (Work.A16.exists_room_of_fix (restG g) (fixes_time g)).choose_spec.choose_spec

lemma as_matrix (g : Lorentz) : (orientation g).val = mat (restG g) := by
  rw [← read_out,mat_room]

lemma factors (g : Lorentz) : boost 0 (b0 g) * (boost 1 (b1 g) *
    (boost 2 (b2 g) * Lorentz.room (orientation g) (oriented g))) = g := by
  rw [read_out]; unfold b0 b1 b2 restG
  repeat' rw [undo_reduce]

lemma rapidity_right (i : SpaceAxis) (g : Lorentz) (k : Ortho) (h : Lorentz.spatialTurn k) :
    rapidity i (g*Lorentz.room k h)=rapidity i g := by
  simp only [rapidity, speed, mat, entry, Lorentz.act_mul, room_time_fixed]

lemma reduce_right (i : SpaceAxis) (g : Lorentz) (k : Ortho) (h : Lorentz.spatialTurn k) :
    reduce i (g*Lorentz.room k h)=reduce i g * Lorentz.room k h := by
  rw [reduce,reduce,rapidity_right, mul_assoc]

lemma orient_right (g : Lorentz) (k : Ortho) (h : Lorentz.spatialTurn k) :
    orientation (g*Lorentz.room k h) = orientation g * k := by
  apply Subtype.ext
  change (orientation _).val = (orientation g).val*k.val
  rw [as_matrix, as_matrix]; unfold restG
  rw [reduce_right,reduce_right 1,reduce_right 2,mat_mul,mat_room]

lemma rapidity_one (i : SpaceAxis) : rapidity i 1=0 := by
  simp [rapidity, speed, mat_one]

lemma reduce_one (i : SpaceAxis) : reduce i 1=1 := by
  simp [reduce, boost, rapidity_one]

lemma orientation_one : orientation 1=1 := by
  apply Subtype.ext
  change (orientation 1).val = (1 : M4)
  rw [as_matrix]; simp only [restG,reduce_one,mat_one]

/- Continuity and along-path differentiability, from global denominators. -/

private lemma artanh_diff {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : DifferentiableAt ℝ artanh x := by
  have he : 0 < 1+x := by linarith [hx.1]
  have hm : 0 < 1-x := by linarith [hx.2]
  have hf : DifferentiableAt ℝ (fun x : ℝ => (1+x)/(1-x)) x :=
    ((differentiableAt_const _).add differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) hm.ne'
  exact (hf.sqrt (div_pos he hm).ne').log (Real.sqrt_pos.2 (div_pos he hm)).ne'

private def coordAt (j k : Axis) : M4→L[ℝ] ℝ := LinearMap.toContinuousLinearMap {
  toFun m := m j k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

lemma rapidity_cont (i : SpaceAxis) : Continuous (rapidity i) := by
  have hv : Continuous (speed i) := ((coordAt i.castSucc timeAxis).continuous.comp mat_continuous).div
    ((coordAt timeAxis timeAxis).continuous.comp mat_continuous) (fun g => (duration_positive g).ne')
  refine continuous_iff_continuousAt.mpr (fun g => ?_)
  exact (artanh_diff (speed_inside i g)).continuousAt.comp hv.continuousAt

lemma reduce_cont (i : SpaceAxis) : Continuous (reduce i) := by
  exact ((Ray.fromAxis i).continuousBoost.comp (rapidity_cont i).neg).mul continuous_id

lemma rest_continuous : Continuous restG := (reduce_cont 2).comp ((reduce_cont 1).comp (reduce_cont 0))

lemma orientation_cont : Continuous orientation := by
  refine continuous_induced_rng.mpr ?_
  simp_rw [Function.comp_def,as_matrix]; exact mat_continuous.comp rest_continuous

lemma rapidity_diff (i : SpaceAxis) {g : ℝ → Lorentz} {x : ℝ} (h : DifferentiableAt ℝ (fun t => mat (g t)) x) :
    DifferentiableAt ℝ (fun t => rapidity i (g t)) x := by
  have he : DifferentiableAt ℝ (fun t => speed i (g t)) x :=
    (((coordAt i.castSucc timeAxis).differentiableAt).comp x h).div
      (((coordAt timeAxis timeAxis).differentiableAt).comp x h) (duration_positive (g x)).ne'
  exact (artanh_diff (speed_inside i (g x))).comp x he

lemma reduce_diff (i : SpaceAxis) {g : ℝ → Lorentz} {x : ℝ} (h : DifferentiableAt ℝ (fun t => mat (g t)) x) :
    DifferentiableAt ℝ (fun t => mat (reduce i (g t))) x := by
  simp_rw [reduce, mat_mul]
  exact (((at_boost i _).differentiableAt).comp x (rapidity_diff i h).neg).mul h

lemma orient_diff {g : ℝ → Lorentz} {x : ℝ} (h : DifferentiableAt ℝ (fun t => mat (g t)) x) :
    DifferentiableAt ℝ (fun t => (orientation (g t)).val) x := by
  simp_rw [as_matrix]; exact reduce_diff 2 (reduce_diff 1 (reduce_diff 0 h))

end YM.Next.BOUNDARY.Descent
