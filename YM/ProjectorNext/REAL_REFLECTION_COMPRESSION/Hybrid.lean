import YM.Next.FREE_KERNELS.Lifts
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Masked
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Stop


set_option warningAsError false

/-!
# Single- and mixed-address hybrid for RGrid approximation

A specialized `Overlay.Bands` scheme. Canonical singleton coordinates,
regular remnants and forced occurrences use their actual `Coefficient`
addresses. The other ranks remain separate with all masks and budgets;
no change of eligible carriers even when selecting markers. Preserve the
address data exactly through k. Each finite probe system permits *all*
subsets. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Marketing
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Marker Overlay Tower Net Masked Stop
open Labels Source
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {G : Gauge} {C : Family G} {p m l N k d : ℕ}

structure Mixed (C : Family G) (N p m l : ℕ) where
  origins : Flags C.path p m → Site (C.side l p)
  support : ℕ → Support (C.side l p)
  rays : ℕ → (Port C p m).Mode
  H : ℕ → Qry C.path p l
  marks : ℕ → ℕ → (Port C p m).Mode
  entries : ℕ → ℕ → Qry C.path p l

abbrev Singles (C : Family G) (p m l d : ℕ) :=
    Flags C.path p m → Coefficient (Masked.R C d) (C.side l p)

abbrev ExpSpace (V : Type*) := V ⊕ ((V × ℕ) ⊕ ℕ)
def expAddr (V : Type*) [Finite V] : ℕ ≃ ExpSpace V := Classical.choice (show Nonempty (ℕ ≃ V ⊕ ((V × ℕ) ⊕ ℕ)) from inferInstance)
def indexAddr (V : Type*) [Finite V] : ℕ ≃ (V ⊕ ℕ) := Classical.choice inferInstance

namespace Mixed
variable (X : Mixed C N p m l)

/- All singleton canonical material represented, including the unit, with its
own hatted mask. Exact correspondence upon output required later. -/
variable (F : Singles C p m l d)
def alphabet (F : Singles C p m l d) (i : ExpSpace (Flags C.path p m)) :
    Support (C.side l p) × (Port C p m).Mode × Qry C.path p l := match i with
  | Sum.inl i => (reach C (X.origins i) d,(Port C p m).fire i,payload C (C.path.rep N p l).p (F i).x (X.origins i))
  | Sum.inr (Sum.inl (i,k)) => ((F i).support k,(Port C p m).fire i,(F i).regular k)
  | Sum.inr (Sum.inr k) => (X.support k, X.rays k,X.H k)

def band (F : Singles C p m l d) : Bands (Port C p m) (C.path.rep N p l) where
  origins := X.origins
  units i := (F i).x 0
  support k := (X.alphabet F (expAddr _ k)).1
  rays k := (X.alphabet F (expAddr _ k)).2.1
  H k := (X.alphabet F (expAddr _ k)).2.2
  marks i j := (indexAddr _ j).elim (Port C p m).fire (X.marks i)
  entries i j := (indexAddr _ j).elim (fun v => (F v).forced i) (X.entries i)

structure Sound : Prop where
  higher i : 2 ≤ (X.rays i).val.card
  pins i j : j ∈ (X.rays i).val → X.origins j ∈ X.support i
  regular i : (C.path.rep N p l).p.Regular (X.support i) (X.H i)
  occurs i j : 2 ≤ (X.marks i j).val.card
  retained i j : X.entries i j ≠ 0 → ∀ s∈ (X.marks i j).val,X.origins s∈ ((C.path.rep N p l).activities.forced i).support
  inspects i j : let B := C.path.rep N p l; UsesFinal B.p.threshold (B.activities.forced i).support (X.entries i j)
  keeps i j U : let B := C.path.rep N p l; X.entries i j U ≠ 0 → (B.activities.forced i).eligible B.p.threshold U
  meas i j : Measurable (X.entries i j)
  gauge i j : GaugeInvariant (X.entries i j)

/-- All other ranks only. Positive reserve δ (if used) for improving radius.
Require also support bounds at the *actual* p.order (non-factorial price)
so transfer must account for those, not just a few derivatives. At forced
costs here e.g. if using κ divisor, feed it through `b`.
-/
structure Invoice (w c b δ : ℝ) : Prop where
  bulk : ∃ t : ℕ → ℝ, (∀ i,0≤t i ∧ ∀ x∈ (X.rays i).val,
      (C.path.rep N p l).p.supBounds (X.origins x) (X.support i) (X.H i) (t i)) ∧
    ∀ i, SumBudget (fun j => if i∈ (X.rays j).val then
      Poly.toll (fun _ => w) (X.rays j)*Mix.loaf (C.path.rep N p l).p (X.support j) δ (t j) else 0) c
  hits : ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤t (i,j) ∧ (0<t (i,j) → X.entries i j≠0) ∧ ∀ x, ‖X.entries i j x‖ ≤ t (i,j)) ∧
    ∀ i, SumBudget (fun k => if i∈ (X.marks k.1 k.2).val then
      Poly.toll (fun _ => w) (X.marks k.1 k.2)*Mix.loaf (C.path.rep N p l).p ((C.path.rep N p l).activities.forced k.1).support δ (t k) else 0) (c*b)


end Mixed
end YM.ProjectorNext.RMirror.Marketing
