import YM.Org.Input
import YM.Phase.Picks
import YM.Phase.Unique




/-! # Ground selection under typed outputs. See docs for
role of witnesses. Uses all *character* inputs tied to unselected.
Read the arrows before trying to re-prove consumers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Org.Phase
open Function Set Filter MeasureTheory Spec Table Extraction OS OS.Ground
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {S : Table C.book} {f : Extraction.Order}

/-- ordinary θ descent, for EVERY all-exterior word. -/
def reflects (V : Chamber S timeAxis) (A : Spread V) := ∀ w : C.book.Word, ∀ h : Word.distinct w,
    M A w h=M A (Grid.anti w) (Grid.apart h)

-- NOTE Grid.anti uses action H (not θ-conj). Applies even for complex labels.
abbrev States (V : Chamber S timeAxis) (A : Spread V) (R : A.Resolution) := R.X→Table C.book

structure Scripts (X : Algebra S) (V : Chamber S timeAxis) (A : Spread V) (R : A.Resolution) (p : States V A R) : Prop where
  reads i : R.receives (p i) i
  loci i : (p i).Hierarchy
  sees i : (p i).respects S
  translations i : X.turns.Oriented (p i)
  incl i : X.derivatives.Inclusions (p i)
  deriv i : X.derivatives.Derivatives (p i)
  fluxes i : StressLaws (p i) X.energy X.derivatives.deriv X.turns.lie

structure Vendor (X : Algebra S) (V : Chamber S timeAxis) (A : Spread V) (R : A.Resolution) : Prop where
  emits : ∃ p, Scripts X V A R p
  bags {p : R.X→Table C.book} (w : Scripts X V A R p) (i) (B : Chamber (p i) timeAxis) :
    ∃ W : Spread B, Spread.Laws W X.derivatives
  -- use a single countable spanning horizon for all α in THIS resolution
  horizon {p : R.X→Table C.book} (w : Scripts X V A R p) (B : ∀ i, Chamber (p i) timeAxis) :
    ∃ W : ℕ→Future C.book timeAxis, ∀ i, Cluster.horizon (B i) W

structure Stall (X : Algebra S) (V : Chamber S timeAxis) (A : Spread V) (f : Order) : Prop where
  spin : reflects V A
  funds : ∀ d (Y : Cells.Columns C S d) (Q : Y.Trials) (h : Cells.Columns.Trials.Valid f Q), Retain.Funds Q h A
  characters : ∃ u : ℕ → A.algebra, DenseRange u
  drives (R : A.Resolution) : R.Out → Vendor X V A R

/-- Separate cases: (1) unselected slab bound & existence (2) with
replicating detectors and UV.GRID use same chamber. -/
structure Loom (s : Seed C f S) (X : Algebra S) (Y : Grill C f) : Prop where
  first : Locals X s.kernel.spin → ∀ V : Chamber S timeAxis,
    ∃ A : Spread V, Spread.Laws A X.derivatives
  sale : Locals X s.kernel.spin → ∀ V : Chamber S timeAxis, ∀ A : Spread V,
    Spread.Laws A X.derivatives → Stall X V A f

namespace Loom
variable {X : Algebra S} {s : Seed C f S} {Y : Grill C f} (H : Loom s X Y) (h : Locals X s.kernel.spin)

include H h
lemma cleanse : ∃ α : Selection S, Materializes (C:=C) X α s.kernel.spin := by
  obtain ⟨V⟩ := OS.realization s.kernel timeAxis
  obtain ⟨A,hA⟩ := H.first h V
  have hp : Stall X V A f := H.sale h V A hA
  have hv : Steady V := fun x i => inert V s.kernel X.turns h.motion _ x
  obtain ⟨u,hu⟩ := hp.characters
  obtain ⟨R,hR⟩ := OS.Ground.resolution A X.turns h.motion s.kernel u hu
  have ht := hp.drives R hR
  obtain ⟨p,B⟩ := ht.emits
  -- choose fixed α chambers before selecting uniqueness. Denote D.
  let D (i : R.X) : Chamber (p i) timeAxis := Classical.choice (OS.realization (B.loci i) _)
  obtain ⟨q,hq⟩ := ht.horizon B D
  obtain ⟨i,hi⟩ := Cluster.selects A D q hq s.kernel hv B.loci hR B.reads
  obtain ⟨W,hW⟩ := ht.bags B i (D i)
  refine ⟨⟨V,A,R,p,i,D i,W⟩,h,hA,hv,hR,B.reads,B.loci,B.translations,fun j d => ?_,B.incl,B.deriv,B.fluxes,hW,hi⟩
  obtain ⟨x,T,H'⟩ := s.corrected d
  exact Retain.lift_detect T H' A R (hp.funds d x T H') hR (B.reads j) (B.loci j).laws.toSymmetric (B.sees j)
end Loom
end YM.Org.Phase
