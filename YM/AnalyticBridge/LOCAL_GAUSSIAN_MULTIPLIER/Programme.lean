import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Alphabet
import YM.Work.B17

/-!
# Multiply on subsets of the edited, physically guarded alphabet

Contracts for the functional inputs to local estimates. When omitting
some of the defaults, can protect readers or pass to analytic branches,
**before** expansion, keeping the actual sector and exact agreement
on the prerequisites. Nonzero use of kept gates including K and forced
seeds still requires the original guards, including the full V flag
agreement from outside, in the identity. Leave any further decisions
(e.g. which witnesses to split into at what occurrence, which factors
MUST be attached to others for component/cover prices and E's
eligibility tests, all attempted tag queries of that dictionary and
their footprint buys) to post-integration reconstruction. This isn't a
statement that any such subsets meet the actual eligibility needs when
reconnecting, or that supplying such priced local readers is doable.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores
open Tree Precision MeasureTheory Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented YM.Push.SectorMeasure.Presented
open scoped Topology BigOperators YM.Push.SectorMeasure Matrix.Norms.Frobenius ContDiff Classical

variable {c f : Side} {G : Gauge} {S : StepData c f} {d : Desk G S}
namespace Spot
variable {u : Spot d}

/-- A variant (e.g. tagged-companion decomposition) of *one*
selected complement. Physical address still not repeated. -/
structure Submenu (F : u.Event) where
  size : ℕ
  buy : Fin size → u.Event
  rebuild V p : u.Clearing V → ∑ i, buy i V p = F V p

def solitary (F : u.Event) : u.Submenu F :=
  { size := 1, buy := fun _ => F, rebuild := fun V p _ => by simp }

/-- Raw guard editing order allows a replacement such as γ (1+h) by
γ (1+hψ) (γ kept unchanged in this equality), without the invalid
premise that after expanding γ into 1+... the individual terms
allow the same replacement. Keep *all* mandatory logs literal, kept
gates may multiply by a bounded protector but cannot drop predicates.
Additional budget prerequisites separate.
-/
structure Programme (D : u.Slices) (b : Finset ℕ) where
  physical : d.Nonoverlap b
  required : Finset (u.Gates b)
  paying : Finset u.Log
  layer : u.Gates b → ℕ
  stored : u.Gates b → u.Event
  posted : u.Log → u.Event
  first V p i : u.Clearing V →
    (∀ j, layer j < layer i → u.gate b j V p ≠ 0) → stored i V p = u.gate b i V p
  original V p i : u.Clearing V → (∀ j, u.gate b j V p ≠ 0) → posted i V p = u.price D i V p
  constPage V p i : u.Clearing V → i ∈ paying → posted i V p = u.price D i V p
  keep V p i : u.Clearing V → i∈required → ∃ ψ : ℝ, ψ∈Icc 0 1 ∧ stored i V p=u.gate b i V p * ψ
  fine i : i∈u.A.costs → (.inl (.inl i)) ∈ required
  noise i : i∈u.A.aisles → (.inl (.inr (.inl i))) ∈ required
  inherit (i : b) : (.inr (.inl i))∈required
  rawG i : u.Submenu (fun V p => stored i V p-1)
  rawLog i : Option (u.Submenu (fun V p => Real.exp (posted i V p)-1))

namespace Programme
variable {D : u.Slices} {b : Finset ℕ} (q : Programme D b)

/-- Helper to construct an arrangement without gate/log rewriting. -/
def inPlace (D : u.Slices) (h : d.Nonoverlap b) (r : Finset u.Log) : Programme D b where
  physical := h
  required := Finset.univ
  paying := r
  layer := fun _ => 0
  stored := u.gate b
  posted := u.price D
  first := by intros; rfl
  original := by intros; rfl
  constPage := by intros; rfl
  keep V p i _ _ := ⟨1,⟨by norm_num,le_rfl⟩,(mul_one _).symm⟩
  fine := by simp
  noise := by simp
  inherit := by simp
  rawG _ := solitary _
  rawLog _ := none







abbrev AtomID := u.Gates b ⊕ u.Log

def freeG := q.requiredᶜ










/-- Raw-paid arguments: a kept mandatory gate, a gate expansion selection,
or a log Mayer variant selection. Price variants literally, not treating
an occurrence as another exp even if only a weak value test on the parent. -/
inductive Stamp : Type
  | heldGate (i : u.Gates b) (h : i∈q.required)
  | billG (i : u.Gates b) (h : i∈q.freeG) (a : Fin (q.rawG i).size)
  | billLog (i : u.Log) (h : i∉q.paying) (M : u.Submenu (fun V p => Real.exp (q.posted i V p)-1))
      (present : q.rawLog i=some M) (a : Fin M.size)

def atom : q.Stamp → AtomID (u:=u) (b:=b)
  | .heldGate i _ | .billG i _ _ => .inl i
  | .billLog i .. => .inr i

def visit : q.Stamp → u.Event
  | .heldGate i _ => q.stored i
  | .billG i _ a => (q.rawG i).buy a
  | .billLog _ _ M _ a => M.buy a

/-- One local list of factors in this expansion. Needn't include EVERY
compulsory gate of the torus, may e.g. be selecting a local portion of the
mandatory packets when there are disjoint components. To require a certain
group of gates for an estimate, must prove still attached in THIS Run.
`one_copy` prohibits repeated address even for marked variants. -/
structure Run (α β γ : Type) where
  entry : α → q.Stamp
  settled : β → u.Log
  marks : γ → u.Log
  settles i : settled i∈q.paying
  unpaid i : marks i∉q.paying
  simple i : q.rawLog (marks i)=none
  one_copy : Function.Injective (Sum.elim (fun i => q.atom (entry i)) (Sum.elim (fun i => Sum.inr (settled i)) (fun i => Sum.inr (marks i))))

namespace Run
variable {q} {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ] (m : q.Run α β γ)
def complete (V : Config G c) (p : u.Visual) :=
    (∏ i, q.visit (m.entry i) V p) * Real.exp (∑ i, q.posted (m.settled i) V p) *
      ∏ i,(Real.exp (q.posted (m.marks i) V p)-1)
end Run
end Programme
end Spot
end YM.AnalyticBridge.LocalGaussian
