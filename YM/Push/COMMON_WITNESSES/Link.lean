import YM.Next.EXTRACTION.Use
import YM.Push.COMMON_WITNESSES.GridMerge
import YM.Push.COMMON_WITNESSES.RankMerge


/-!
# Link common stations at RArrives, RBase, RSeed, RGrill

Keep raw S and the same M p at *every* fixed p. We also really require
projection convergence at every p (and then in the outer limit) and exactly
the connected Differential plan from Base. C includes fields (readout as in
Makes, C.ref and C.refUnit, same C.S etc) once for all.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Common
open Function Filter Set Extraction Cells Wilson Table Next.Extract Dash
open scoped Topology BigOperators

variable {G : Gauge}

/-- Witnesses of the raw port. -/
structure Snap (C : Family G) where
  S : Table C.book
  M : ℕ → Table C.book
  R : Bin S
  z : ∀ d, ℕ → CoordMap C d

variable {C : Family G}

namespace Snap
structure First (w : Snap C) (b : Presentation C) (f : Order) : Prop where
  family : C.Makes
  center : CenterPort C f
  raw : RawLimits C f w.S w.M
  projections : Projected b f w.R w.z

/-- Additional witnesses from continuum extraction. -/
structure Upper (w : Snap C) where
  T : Table C.book
  V : DiffPlan T
end Snap
open Snap

variable {w : Snap C}

/-- Through RBase, retaining the same projections/spans. Keep quantitative
finite RBin/Short invoices (which themselves have existence quantifiers as in
NEXT, but don't leave the extraction). -/
structure Risen (c : Upper w) (b : Presentation C) (f : Order) : Prop where
  base : Base C f w.S w.M w.R c.T c.V
  projections : Projected b f w.R w.z
  relays d : RelayCosts b f d
  det d : Detector b f d

namespace Risen
variable {c : Upper w} {b : Presentation C} {f g : Order}

lemma first (H : Risen c b f) : First w b f := ⟨H.base.family,H.base.center,H.base.arrives.census,H.projections⟩

/-- Transport on refinement -- NOT rerunning the data constructors (which
might keep only some equivalent points of the tables, for instance). Uses
even the NEXT relay cost transport (for rows newly satisfying tail estimates
*only* on the later station). -/
lemma upon (H : Risen c b f) (h : Tails g f) : Risen c b g :=
  ⟨h.base H.base,h.projected H.projections,fun d => h.relay (H.relays d),fun d => h.detects (H.det d)⟩
end Risen

structure Holder (T : Table C.book) where
  X : Offers T
  innerLimits (d : ℕ) : ProbeID (X.cols d) → ℕ → C.label d

variable {T : Table C.book}

abbrev Holder.Income (A : Holder T) (b : Presentation C) (f : Order) : Prop :=
  A.X.affords b f A.innerLimits

/-- Quantitative phase prerequisites and ALL the data. -/
structure Guests (T : Table C.book) where
  plate : Holder T
  menu : Menu
  figs : GridBooks C

variable {c : Upper w} {b : Presentation C} {f : Order}

structure Hosted (c : Upper w) (b : Presentation C) (Y : Guests c.T) (f : Order) : Prop where
  atBase : Risen c b f
  ranks : Y.plate.Income b f
  rails : Sustained C Y.menu Y.figs f

namespace Hosted
variable {Y : Guests c.T}
lemma upon (H : Hosted c b Y f) {g} (h : Tails g f) : Hosted c b Y g :=
  ⟨H.atBase.upon h,fun i => (H.ranks i).upon h,H.rails.upon h⟩
lemma seed (H : Hosted c b Y f) : Spec.Seed C f c.T :=
  H.atBase.base.seed (valid_offers H.ranks)
lemma grill (H : Hosted c b Y f) : Org.Grill C f := ready_grill _ _ _ H.rails
end Hosted

/-!
Commit multiple calls in the right order. Any estimate requested *within a
tower of an extraction* will be used on a genuine further extraction required
by the next service. Two independently selected refinements is not a feasible
protocol. -/

theorem rise (H : w.First b f) (hq : Stationed f (fun d g => RelayCosts b g d ∧ Detector b g d)) :
    ∃ g : Order, ∃ c : Upper w, Risen c b (f.refine g) := by
  obtain ⟨g,hg⟩ := hq.collect (fun _ _ _ h hq => ⟨h.relay hq.1,h.detects hq.2⟩)
  have hp := Tails.refine f g
  obtain ⟨T,V,hV⟩ := finish H.family (hp.center H.center) (hp.raw H.raw) (hp.projected H.projections)
    (fun d => (hg d).1) (fun d => (hg d).2)
  exact ⟨g,⟨T,V⟩,hV,hp.projected H.projections,fun d => (hg d).1,fun d => (hg d).2⟩




end YM.Push.Common
