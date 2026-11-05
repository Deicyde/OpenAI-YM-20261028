import YM.Cells.Cut
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Cut a torus into transverse matrices and time-link thread

 ff. Approach both chess reflection and cutoff JLips via this
specific decomposition. Positive time pointing `C.pos` by the axis choice.
No zero-mode projection here; probabilities throughout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Slice
open Function Set MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} (a : Axis)

/-- Transverse directions use their actual positive orientation. -/
abbrev Flat (a : Axis) := {i : Axis // i ≠ a}
abbrev Row (a : Axis) (n : Side) := Flat a → Per n
abbrev Tile (a : Axis) (n : Side) := Row a n × Flat a

abbrev Leaf (G : Gauge) (a : Axis) (n : Side) := Tile a n → G.El
abbrev Thread (G : Gauge) (a : Axis) (n : Side) := Row a n → G.El
abbrev Layer (G : Gauge) (a : Axis) (n : Side) := Leaf G a n × Thread G a n
abbrev Circle (G : Gauge) (a : Axis) (n : Side) := Per n → Layer G a n

def plane (t : Per n) (v : Row a n) : Site n := fun i => if h : i=a then t else v ⟨i,h⟩
def drop (x : Site n) (t : Flat a) := x t

@[simp] lemma plane_pos (t : Per n) (v) : plane a t v a=t := by simp [plane]
@[simp] lemma plane_row (t : Per n) (v) (i : Flat a) : plane a t v i=v i := by simp [plane,i.property]
@[simp] lemma dropped (t : Per n) (v) : drop a (plane a t v)=v := by funext i; simp [drop]
@[simp] lemma plane_from (x : Site n) : plane a (x a) (drop a x) = x := by
  funext i; rcases eq_or_ne i a with h|h <;> simp [h,plane,drop]

@[simp] lemma lift_time (t : Per n) (v) : plane a t v + step a = plane a (t+1) v := by
  funext i; rcases eq_or_ne i a with h|h <;> simp [plane,h]

def forward (v : Row a n) (p : Flat a) : Row a n := v+Pi.single p 1

@[simp] lemma shift (t : Per n) (v : Row a n) (p : Flat a) : plane a t v + step p.val = plane a t (forward a v p) := by
  funext i; rcases eq_or_ne i a with h|h
  · simp [h,Ne.symm p.property]
  change _ = plane a t _ (⟨i,h⟩ : Flat a)
  rw [plane_row]; change plane a _ _ (⟨i,h⟩ : Flat a) + _ = _
  rw [plane_row]; simp [forward, step_apply, Pi.single_apply,Subtype.ext_iff,eq_comm]

def leaves (U : Config G n) : Circle G a n := fun t =>
  (fun p => U (plane a t p.1,p.2), fun p => U (plane a t p,a))

def chain (F : Circle G a n) (e : Edge (Site n)) : G.El :=
  if h : e.2=a then (F (e.1 a)).2 (drop a e.1) else (F (e.1 a)).1 (drop a e.1,⟨e.2,h⟩)

@[simp] lemma chain_space (F : Circle G a n) (t : Per n) (v) (b : Flat a) :
    chain a F (plane a t v,b) = (F t).1 (v,b) := by simp [chain,b.property]

@[simp] lemma chain_time (F : Circle G a n) (t : Per n) (v) :
    chain a F (plane a t v,a) = (F t).2 v := by simp [chain]

def slice : Config G n ≃* Circle G a n where
  toFun := leaves a
  invFun := chain a
  left_inv x := by
    funext i
    rcases i with ⟨v,i⟩
    unfold chain leaves
    dsimp only
    by_cases h : i=a
    · subst i; simp
    simp [h]
  right_inv f := by
    funext i
    apply Prod.ext
    · ext1 j; exact chain_space ..
    exact funext fun j => chain_time ..
  map_mul' _ _ := rfl

@[fun_prop] lemma leaves_cont : Continuous (leaves (G := G) (n := n) a) := by
  unfold leaves; fun_prop
@[fun_prop] lemma chain_cont : Continuous (chain (G := G) (n := n) a) := by
  refine continuous_pi fun i => ?_
  unfold chain; split <;> fun_prop

-- all volume adapters use actual probHaar, no independent definition.
variable (G n) in
def trans := Measure.pi fun _ : Tile a n => G.probHaar
variable (G n) in
def threads := Measure.pi fun _ : Row a n => G.probHaar

variable (G n) in
def layerLaw := (trans n G a).prod (threads n G a)
variable (G n) in
def spread := Measure.pi fun _ : Per n => layerLaw n G a

instance : IsProbabilityMeasure (trans n G a) := by unfold trans; infer_instance
instance : IsProbabilityMeasure (threads n G a) := by unfold threads; infer_instance
instance : IsProbabilityMeasure (layerLaw n G a) := by unfold layerLaw; infer_instance
instance : IsProbabilityMeasure (spread n G a) := by unfold spread; infer_instance

section
instance : BorelSpace (Leaf G a n) := by unfold Leaf; infer_instance
instance : BorelSpace (Thread G a n) := by unfold Thread; infer_instance
instance : BorelSpace (Layer G a n) := by unfold Layer Leaf Thread; infer_instance
instance : BorelSpace (Circle G a n) := by unfold Circle Layer Leaf Thread; infer_instance
open Measure
instance : IsHaarMeasure (trans n G a) := by unfold trans; constructor
instance : IsHaarMeasure (threads n G a) := by unfold threads; constructor
instance : MeasurableMul (Leaf G a n) := by unfold Leaf; infer_instance
instance : MeasurableMul (Thread G a n) := by unfold Thread; infer_instance
instance : MeasurableMul (Layer G a n) := by unfold Layer; infer_instance
instance : IsHaarMeasure (layerLaw n G a) := by unfold layerLaw; exact Measure.prod.instIsHaarMeasure (G := Leaf G a n) (H := Thread G a n) (trans n G a) (threads n G a)
instance : IsHaarMeasure (spread n G a) := by unfold spread; constructor
instance : IsHaarMeasure (prior G n) := by unfold prior; constructor
end

lemma leaves_volume : MeasurePreserving (leaves a) (prior G n) (spread n G a) :=
  MonoidHom.measurePreserving (f := (slice (n := n) (G := G) a).toMonoidHom) (leaves_cont a) (slice (n := n) (G := G) a).surjective (by simp)

lemma chain_volume : MeasurePreserving (chain a) (spread n G a) (prior G n) :=
  MonoidHom.measurePreserving (f := (slice (n := n) (G := G) a).symm.toMonoidHom) (chain_cont a) (slice (n := n) (G := G) a).symm.surjective (by simp)

end YM.Slice
