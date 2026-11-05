import YM.UVNext.FREE_STRESS_CERTIFICATE.Size
/-! Signed permutations exchanging two quadratic plane monomials on a parity class. -/
noncomputable section
set_option autoImplicit false
namespace YM.Pert.Rigid
open Function UVNext.FreeStress Classical
abbrev Edge := Axis × Axis
abbrev Slate := Edge×Edge

def tape (c : Face) : Slate := (c.val.1.val,c.val.2.val)
def same (p q : Edge) : Prop := p=q ∨ p=q.swap
def Same (c d : Slate) : Prop := same c.1 d.1 ∧ same c.2 d.2 ∨ same c.1 d.2 ∧ same c.2 d.1
instance (p q : Edge) : Decidable (same p q) := by unfold same; infer_instance
instance (p q : Slate) : Decidable (Same p q) := by unfold Same; infer_instance

def mapEdge (f : Axis → Axis) (p : Edge) : Edge := (f p.1,f p.2)
def mapSlate (f : Axis → Axis) (c : Slate) : Slate := (mapEdge f c.1,mapEdge f c.2)
def pop (p : Edge) (a : Axis) : Bool := decide (p.1=a ∨ p.2=a)
def paint (c : Slate) (a : Axis) : Bool := pop c.1 a != pop c.2 a -- != is Bool cast?
def camp (c : Face) : Bool := (tape c).1 == (tape c).2

abbrev northWest (i j : Axis) := Equiv.swap i j
def swings : Fin 10 → Equiv.Perm Axis := Fin.cons (Equiv.refl _) <| Fin.cons (northWest 0 1) <| Fin.cons (northWest 0 2) <| Fin.cons (northWest 0 3) <| Fin.cons (northWest 1 2) <| Fin.cons (northWest 1 3) <| Fin.cons (northWest 2 3) <| Fin.cons ((northWest 0 1).trans (northWest 2 3)) <| Fin.cons ((northWest 0 2).trans (northWest 1 3)) <| Fin.cons ((northWest 0 3).trans (northWest 1 2)) Fin.elim0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
lemma swingTest : ∀ (i : Fin 10) (a : Axis), (swings i (swings i a))=a := by decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 20000000 in
theorem havePath : ∀ c d : Face, paint (tape c) = paint (tape d) → (∃ i : Fin 10, Same (mapSlate (swings i) (tape c)) (tape d) ∧ Same (mapSlate (swings i) (tape d)) (tape c)) ∧ camp c = camp d := by decide

end YM.Pert.Rigid
