import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Words
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding

/-!
# Authentic signed motion of the input k charts

Extended G06 geometry (positive Slot, BEFORE suppression); preserve the
face covariance's canonical positive addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift.Compass
open Filter Function Set Lattice Wilson RG Source Source.Drops Labels Cells Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open  Work.G06
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {P : BudgetPoint} {d t : ℕ}

-- oriented circulation price
private def polarity (a b : Lattice.Step) : ℝ :=
  (if a.dir<b.dir then 1 else -1)*(if a.neg then -1 else 1)*(if b.neg then -1 else 1)

def wind (s : Signed) (p : PlaqAxes) : ℝ := polarity ((posDir p.val.1).rotate s) ((posDir p.val.2).rotate s)

lemma wind_sq (s : Signed) (p : PlaqAxes) : wind s p * wind s p=1 := by unfold wind polarity; split_ifs <;> ring

private lemma positive_corner (w : Walk) (a b : Axis) (h : a≠b) (U : CoverConfig G) :
    slanted w (posDir a) (posDir b) U= (if a<b then (1:ℝ) else -1) • (⟨w,PlaqAxes.ordered a b h⟩:Slot).eval U := by
  rw [slot_pos]; unfold PlaqAxes.ordered; change _=_ • slanted w (posDir (min a b)) (posDir (max a b)) U
  rcases lt_or_gt_of_ne h with H|H
  · rw [if_pos H,min_eq_left H.le,max_eq_right H.le,one_smul]
  rw [if_neg H.not_gt,min_eq_right H.le,max_eq_left H.le,neg_one_smul,slanted_swap w (posDir a),neg_neg]

private lemma reversed (a b : Axis) (h : a≠b) :
    PlaqAxes.ordered b a h.symm=PlaqAxes.ordered a b h := by apply Subtype.ext; simp [PlaqAxes.ordered,min_comm,max_comm]
private lemma swapped (a b : Axis) (h : a≠b) :
    (if b<a then (1:ℝ) else -1) = -(if a<b then 1 else -1) := by
  rcases lt_or_gt_of_ne h with h|h
  · rw [if_pos h,if_neg h.not_gt]
  rw [if_neg h.not_gt,if_pos h,neg_neg]

private lemma slant_mark (w : Walk) (a b : Lattice.Step) (h : a.dir≠b.dir) :
    ∃ v : Slot, v.plaq=PlaqAxes.ordered a.dir b.dir h ∧
      v.offset=atFace (stop (0:Cover) w) a b ∧ v.walk.length≤w.length+2 ∧
        ∀ U : CoverConfig G, slanted w a b U = polarity a b • v.eval U := by
  rcases a with ⟨i,_|_⟩ <;> rcases b with ⟨j,_|_⟩ <;> change i≠j at h
  · refine ⟨⟨w,PlaqAxes.ordered i j h⟩,rfl,by simp [Slot.offset,atFace],by simp,fun U => ?_⟩
    simp only [polarity, Bool.false_eq_true, ↓reduceIte, mul_one]; exact positive_corner w i j h U
  · refine ⟨⟨w++[negDir j],PlaqAxes.ordered i j h⟩,rfl,by simp [Slot.offset,atFace,stop_append,stop]; rfl,by simp,fun U => ?_⟩
    change slanted w (posDir i) (negDir j) U=_
    rw [slanted_swap w (negDir j),← slanted_next w,Step.rev_neg, positive_corner _ i j h]
    simp [polarity]
  · refine ⟨⟨w++[negDir i],PlaqAxes.ordered i j h⟩,rfl,by simp [Slot.offset,atFace,stop_append,stop]; rfl,by simp,fun U => ?_⟩
    change slanted w (negDir i) (posDir j) U=_
    rw [← slanted_next w, Step.rev_neg, positive_corner _ j i h.symm, reversed i j h, swapped i j h]; simp [polarity]
  refine ⟨⟨(w++[negDir i])++[negDir j],PlaqAxes.ordered i j h⟩,rfl,by simp [Slot.offset,atFace,stop_append,stop]; rfl,
    by simp,fun U => ?_⟩
  change slanted w (negDir i) (negDir j) U= _
  rw [← slanted_next w,← slanted_next (w++_), Step.rev_neg, Step.rev_neg,positive_corner _ i j h]; simp [polarity]

lemma worth (w : Walk) (a b : Lattice.Step) (h : a.dir ≠ b.dir) :
    ∃ (v : Slot) (x : ℝ), v.walk.length ≤ w.length+2 ∧ (x=1 ∨ x=-1) ∧
      ∀ U : CoverConfig G, slanted w a b U=x • v.eval U := by
  obtain ⟨v,-,-,he,h⟩ := slant_mark (G:=G) w a b h
  exact ⟨v,polarity a b,he,by unfold polarity; split_ifs <;> norm_num,h⟩

private lemma wrap_corner (n : Side) (x : Cover) (a b : Lattice.Step) :
    wrap n (atFace x a b) = atFace (wrap n x) a b := by
  unfold atFace; rw [map_add,map_add]
  cases h : a.neg <;> cases he : b.neg <;> simp [wrap_vec]

private lemma rebase_mark (s : Signed) (x : Cover) (w : Walk) :
    stop (s.act x) (w.map (·.rotate s))=s.act (stop x w) := by
  induction w generalizing x <;> simp_all only [stop,List.map_nil,List.map_cons, Step.vec_rotate, ← Signed.act_add]

lemma stamp (v : Slot) (s : Signed) : ∃ z : Slot, z.walk.length ≤ v.walk.length+2 ∧
    (∀ U : CoverConfig G, v.eval (pull s 0 U)=wind s v.plaq • z.eval U) ∧
    ∀ (n : Side), ((wrap n z.offset,z.plaq):Face (Per n)) = Face.send s (0:Site n) (wrap n v.offset,v.plaq) := by
  obtain ⟨z,hz,he,hL,h⟩ := slant_mark (G:=G) (v.walk.map (·.rotate s)) ((posDir v.plaq.val.1).rotate s)
      ((posDir v.plaq.val.2).rotate s) (s.perm.injective.ne v.plaq.property.ne)
  refine ⟨z,by simpa using hL,fun U => ?_,fun n => Prod.ext ?_ hz⟩
  · rw [slot_pos, slanted_pull]; exact h _
  change wrap n z.offset = Face.lower _ _ _
  rw [he, wrap_corner]
  have hw := rebase_mark s 0 v.walk; rw [Signed.act_zero] at hw; rw [hw]; unfold Face.lower
  apply congr_arg (fun x => atFace x _ _); simp [affine,Slot.offset]
end YM.Further.CorrectedLift.Compass
