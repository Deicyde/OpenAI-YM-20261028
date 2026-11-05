import YM.Next.RANK.Incoming
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Stepped
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.Next.RANK.Incoming for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Peak
open Lattice Wilson RG Value Perch Filter Set Function Marker Glyph Extraction Market Ship Cells Read  Dock Camp Station
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {m k p N v : ℕ} {Z : Demand}
variable {C : Family G} {S : Table C.book} {b : ℝ}

section
variable (hi : k ≤ N) {x : Points v}
variable (Y : Course C N p k) (P : (u : ℕ) → Rep G (C.side u p))
variable (D : Era)
variable (B : Fin v→ (standard C).Tag) (t : Fin v→ C.book.Token)
variable (ho : FitSky C.path.levels b k x)

-- Remaining local W physics at l. This estimate is unweighted and for the actual C.cost of inquiry.
-- Need also true geometry of W occurrence. No masks in value defines W, all tests on full support.

def ArrangementsSky (c : Demand) (m : ℕ) :=
    let A := C.path.levels
    let s := A.clock.hatBeta k
    let l := middleSky A b k
    let u := A.clock.hatBeta l
    let T := yardSky C b hi p
    let P' := P l
    let g := (P' : Rep G (A.S.side l p)).p
    let y : l≤N := (beforeSky A b k).trans hi
    let read := Ship.clients C t b k N p x
    let L := Ship.targetsSky C B ho
    let ζ := readersSky (C:=C) (b:=b) (p:=p) x hi y
    ∀ h : g.B = walls u, ∀ hv : Shelf c m s u,
      let J := Meter A h hv
      ∃ (α β : Type), ∃ (_ : Fintype α) (_ : Fintype β), ∃ (H : α → SourceAt G ζ) (K : β → Lifted G ζ g.threshold)
        (W : T.Cell × flame (Fin v) → SourceAt G ζ),
        Reception J H K ∧ Background P' K ∧ Y.flow (Array.stamp T (C.beta N p) (bareP read)) _ y=dust P' (Sum.elim H W) K ∧
          ∀ i,(W i).fires=sectionAt i ∧ (W i).extent=Peak.routeSky A b k p c.Q g.B i.1 ∧ ∀ U,
            Healthy g.threshold (Peak.routeSky A b k p c.Q g.B i.1) U → ‖(W i).value U+view T L i‖≤Perch.bill (-31/32) s

/-- Conditional request per row at a stamp N. Additional offset routings not claimed. -/
def InstanceSky (nslot : ℕ) :=
    ArrangementsSky hi Y P B t ho D.coast nslot ∧ ExhibitsSky Y P b x nslot hi (Ship.invoiceSky B t ho N p) D

end

-- Ready use ON A. Numerical gate proven feasible separately. Does not accept from J predecessor if used with different K.
structure ChargeSky (a : Levels G) (b : ℝ) (k slot : ℕ) (O : HaarBudget G) (D : Era) : Prop where
  allot : AllocatedSky a slot k O b
  tally : Tally (wheelSky a k) (a.clock.hatBeta k) D slot
  assured u : widthSky a b k ≤ u → u≤middleSky a b k → a.clock.hatBeta u ∈ Icc (a.clock.hatBeta k/2) (a.clock.hatBeta k)

variable (O : HaarBudget G) {d : ℕ} (X : Columns C S d)

open Dash Org Spec Bid

end YM.Next.Rank.Peak
