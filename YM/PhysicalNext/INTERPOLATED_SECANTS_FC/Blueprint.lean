import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Crowns
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Kite
import YM.Extra.WILSON_STARTUP.Clock
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Reset
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial


/-!
# Coefficient interface on one CONNECTED_ACTIVITY_BOUNDS operation

Exact candidate layout sufficient for the estimates (see `Layout` and `VerifiedReset.Inputs`).
Coherently split the actual first integrated **unforced** species only into weighted anchored
variants; forced seeds remain single. Additional E and discrepancy families from alignment of
paths/low powers are upstream, not uniquely prescribed by the sum. This is ONE option, not an
identity between independently produced atlases. Shared Secant endpoints, forest distribution &
hat scales; *even if* disjoint words, no assuming product and this average commute.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InterpolatedSecantsFc
open Function Filter Finset Set Lattice RG Wilson Precision Pressure Pressure.Stores Tree Push.SectorMeasure
  Push.AbsoluteSums AnalyticNext.ConnectedActivity AnalyticNext.ConnectedActivity.Cab Ursell
  AnalyticBridge.VerifiedReset
open scoped Classical Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f}

structure Payload (G : Gauge) (f : Side) where
  E : ℕ → Field G f
  K : ℕ → Field G f
  v : ℝ



def replay (R : RG.Rep G f) (β : ℝ) (h : Payload G f) : RG.Rep G f :=
  {R with beta := β, v := h.v, activities := {R.activities with E := h.E,K := h.K}}


def segment (v w : Payload G f) (t : ℝ) : Payload G f where
  E i U := t * v.E i U + (1-t)*w.E i U
  K i U := t * v.K i U + (1-t)*w.K i U
  v := t*v.v + (1-t)*w.v



structure Mixture (S : StepData c f) where
  forests : Finset (Forest S.ratio)
  degree : Forest S.ratio → ℝ
  pos F : F ∈ forests → 0 ≤ degree F
  unit : ∑ F∈forests, degree F = 1
namespace Mixture
variable (M : Mixture S)
def average (g : Forest S.ratio → ℝ) := ∑ F∈M.forests,M.degree F * g F


end Mixture

section Shape
variable (T : Tube G S) (R : RG.Rep G f) (x : ℝ)
abbrev bus := buses T R x
abbrev Zone := Zones T R x
abbrev Onsite := (i : Zone T R x) × {o // o ∈ bus T R x i}
abbrev HardSeed := {i : Zone T R x // ¬untapped S i.val}

def idAtom (i : Onsite T R x) : RegularAddress c := ⟨i.2.val,bus T R x i.1,i.2.property⟩
lemma seed_owned (i : Finset (Cab.Tab S)) : (storeAt S i).flags ⊆ surface S T R x i := by
  intro t ht
  obtain ⟨A,hA,ht⟩ := Finset.mem_biUnion.mp (mem_toRight.mp (mem_toRight.mp ht))
  have hp : t∈ A.flags := inr_mem_disjSum.mp (inr_mem_disjSum.mp ht)
  exact mem_biUnion.mpr ⟨Sum.inl A,mem_toLeft.mp hA,show t∈A.dome (500*radiusB x) from halo_subset _ _ (mem_union_right _ hp)⟩
/-- Retain the old selection/test even inside a merger (on all amplitude comparisons the
`Preceded` decision uses only immutable incoming data). -/
def idSeed (i : HardSeed T R x) : ForcedAddress G c :=
    ⟨bus T R x i.val,(storeAt S i.val.val).flags,Finset.nonempty_iff_ne_empty.mpr i.property,seed_owned T R x _,Preceded T R x i.val.val⟩
end Shape

variable {T : Tube G S} {R : RG.Rep G f} {x : ℝ}
structure Geography (T : Tube G S) (R : RG.Rep G f) (x : ℝ) where
  mixture : Mixture S
  share : Onsite T R x → ℝ
  nonneg i : 0 ≤ share i
  sum i : ∑ o, share ⟨i,o⟩ = 1
  aligned : ℕ → RegularAddress c
  attachment : ℕ → Support c
  visited i : (attachment i).Nonempty
  padding : ℕ → ForcedAddress G c
namespace Geography
variable (A : Geography T R x)
def layout : Placement G c (Onsite T R x) (HardSeed T R x) where
  atom := idAtom T R x
  seed := idSeed T R x
  aligned := A.aligned
  attachment := A.attachment
  visited := A.visited
  padding := A.padding

def shelf : Shelf G c (Onsite T R x) (HardSeed T R x) := Shelf.canonical A.layout
end Geography

/-- Missing upstream coefficients and immutable reads etc. `unforced` MUST reproduce the
actual integrated first amplitudes (possibly after summing genuine choices), pre-mask germs
and correspondence including at equality stencils. `approx` and `fresh` house the signed
low-grade pieces on either side of the path/loop prescription alignment, in normalized powers.
-/
structure Blueprint (T : Tube G S) (R : RG.Rep G f) (x : ℝ) extends Geography T R x where
  unforced : ℝ → Payload G f → Onsite T R x → Field G c
  approx : Clusters (Onsite T R x) → Powers G c
  fresh : ℕ → Powers G c
  move : ℕ → Powers G c
namespace Blueprint
variable (L : Blueprint T R x) (W r : ℝ) (N : ChartRatio G) (B : Chi)

def content : Content G c (Onsite T R x) (HardSeed T R x) (Payload G f) where
  unforced := L.unforced
  forced b h i U := L.mixture.average fun F => Cab.centre T x W r N (replay R b h) F B i.val.val U
  approx := L.approx
  fresh := L.fresh
  move := L.move
abbrev rack := L.toGeography.shelf
abbrev X := L.rack.toPlacement





end Blueprint
end YM.PhysicalNext.InterpolatedSecantsFc
