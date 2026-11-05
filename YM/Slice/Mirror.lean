import YM.Slice.Hamilton

/-!
# Reflect layered arrays without hiding sign/order

Holds for link or site cuts on actual lattice. Gauge in Leaf acts at
both transverse locations. Correct placement of temporal integration:
Y gauge averaged by *one common thread* u (vertex family), not one
independent per-link transform.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set Filter MeasureTheory
open Lattice Wilson Cells
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder

variable {n : Side} {G : Gauge} (C : Cut n)

def level (t : Per n) := 2*C.baseLine - (C.kind.shift : Per n) - t
@[simp] theorem level_twice (t : Per n) : level C (level C t) = t := by unfold level; ring

@[simp] theorem image_plane (t : Per n) (v) :
    C.reflect (plane C.pos t v) = plane C.pos (level C t) v := by
  ext1 a; by_cases he : a=C.pos
  · simp [he,level]
  rw [C.reflect_there _ he]; simp [plane,he]

theorem inv_layer (V : Circle G C.pos n) (t x) :
    (leaves C.pos (C.pullC G (chain C.pos V)) t).2 x = ((V (level C t - 1)).2 x)⁻¹ := by
  change ((posDir C.pos).rotate (Signed.mirror C.pos)).read _ (C.reflect (plane C.pos t x)) = _
  rw [image_plane, show (posDir C.pos).rotate (Signed.mirror C.pos) = negDir C.pos by simp [Step.rotate,posDir,negDir,Signed.mirror],Step.neg_read]
  rw [show plane C.pos (level C t) x - step C.pos = plane C.pos (level C t-1) x by
    rw [sub_eq_iff_eq_add]; simp]
  simp

theorem fixed_plane (V : Circle G C.pos n) (t) :
    (leaves C.pos (C.pullC G (chain C.pos V)) t).1 = (V (level C t)).1 := by
  ext1 v
  change ((posDir v.2).rotate (Signed.mirror C.pos)).read _ (C.reflect (plane C.pos t v.1)) = _
  rw [image_plane, show (posDir v.2.val).rotate (Signed.mirror C.pos) = posDir v.2.val by
    simp [Step.rotate,posDir, Signed.mirror,Ne.symm v.2.property], Step.pos_read,chain_space]

def opposite (V : Circle G C.pos n) : Circle G C.pos n := fun t =>
  ((V (level C t)).1, ((V (level C t - 1)).2)⁻¹)

@[simp] theorem mirrors (V : Circle G C.pos n) : C.pullC G (chain C.pos V) = chain C.pos (opposite C V) := by
  apply (slice _).injective
  change leaves C.pos (C.pullC G (chain C.pos V)) = _
  rw [show (slice C.pos (chain C.pos _)) = _ from (slice C.pos).apply_symm_apply _]
  exact funext fun t => Prod.ext (fixed_plane ..) (funext fun _ => inv_layer ..)

theorem backs (V : Circle G C.pos n) (β) (t) : weight C.pos β (opposite C V t).1
    (opposite C V (t+1)).1 (opposite C V t).2 = weight C.pos β (V (level C t-1)).1
    (V (level C t)).1 (V (level C t-1)).2 := by
  unfold opposite
  simp only [show level C (t+1) = level C t - 1 from by unfold level; ring, weight_reflect]

variable (a : Axis)
def repaint (X : Leaf G a n) (u : Thread G a n) : Leaf G a n := fun p =>
  u p.1 * X p * (u (forward a p.1 p.2))⁻¹

@[fun_prop] lemma repaint_cont : Continuous fun p : Leaf G a n × Thread G a n => repaint a p.1 p.2 := by
  unfold repaint; fun_prop

@[simp] lemma repaint_one (X : Leaf G a n) : repaint a X 1 = X := by ext; simp [repaint]

@[simp] lemma repaint_split (X : Leaf G a n) (u v) : repaint a (repaint a X u) v = repaint a X (v*u) := by
  ext; simp [repaint, mul_assoc]

private lemma forward_comm (x : Row a n) (b c : Flat a) : forward a (forward a x b) c = forward a (forward a x c) b := by
  unfold forward; abel

theorem cost_same (X : Leaf G a n) (u) : potential a (repaint a X u)=potential a X := by
  unfold potential
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨x,⟨b,c⟩, hb⟩ := i
  rw [show smallLoop a (repaint a X u) (x,⟨(b,c),hb⟩) = u x * smallLoop a X (x,⟨(b,c),hb⟩) * (u x)⁻¹ by
    simp [smallLoop, repaint,forward_comm a x b c,mul_assoc]]
  exact G.price_conj _ _

lemma weight_second (β) (X Y : Leaf G a n) u :
    weight a β X Y u = weight a β X (repaint a Y u) 1 := by
  rw [weight,weight,evenPart,evenPart,evenPart,cost_same]
  rw [show transition a X (repaint a Y u) 1 = transition a X Y u by
    unfold transition
    apply Finset.sum_congr rfl; intro i _; simp [connect,repaint,mul_assoc]]

theorem together (β) (X Y : Leaf G a n) (u) :
    weight a β (repaint a X u) (repaint a Y u) 1 = weight a β X Y 1 := by
  rw [← weight_second, ← weight_reflect a β, weight_second, repaint_split, inv_mul_cancel,repaint_one,
    ← weight_reflect]; simp
end YM.Slice
