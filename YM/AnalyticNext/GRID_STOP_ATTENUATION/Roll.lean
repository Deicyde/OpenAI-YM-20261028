import YM.AnalyticNext.GRID_STOP_ATTENUATION.Annual
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Gate
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Neighbors
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Ways
import YM.Push.GRID_APPROXIMATION.Candidates



set_option warningAsError false

/-!
# Down at one actual grid

Reach `Receipt`, per-cutoff.

Weaker option than requiring a solution to the normalized
rank-local price problem for arbitrary Credit inputs/outputs at every step --
inserts are matched on this very path, can use their structure (incl above
the stop) to produce `UnitTest`.

But it must support the actual
prescription even encountering the first inlet at the fork k.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Stock
open Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {d k r h p N : ℕ}

abbrev System (C : Family G) (h p : ℕ) := Site (C.side h p)
abbrev Ranks (C : Family G) (h p : ℕ) := Joint.Markers C.path h p

variable (B : Pair.Probe C N p d k) (v : C.label d)

def keyed {i : ℕ} (hi : h ≤ i) (x : System C h p) : Multi.Pulse G (C.side i p) :=
    Pair.pulse B (Pair.spin C v x) i (anchor C.S p hi x)

/-- Total (scaled and before integration) on this same grid match. -/
def wave {i : ℕ} (hk : h ≤ k) (hN : k≤N) (hi : i ≤ k) :=
    Joint.scaled C.path N p hk hN (C.O N p v 0) (candidate C k p d (Pair.tune B v)) hi d

-- initial small radius data authenticated in same history
variable (h k)
/-- Fork certificate: spend JUST Active and Radial here, on the path's
chosen unmarked vocabulary. Top pricing planner separate. This case
allows k=N at each late station. -/
structure Inlet (q : h≤k) (hN : k≤N) {u : System C h p → ℝ}
    (A : Bands (Ranks C h p) (C.path.rep N p k)) (c t f b : ℝ) : Prop where
  valid : A.Active
  began : A.Radial u c t f b
  origins : A.origins=anchor C.S p q
  exactAt (s : (Ranks C h p).Mode) : (fun U => (A.density U).part s) = wave B v q hN (le_refl k) s

variable {h k}

/-- Induct only testing pre-scales for the representation actually compatible
with the paid grid. `fires` fixes the alphabet on singletons: requires the
inlet catalog at k, and comparison prescription (not necessarily that same
presentation) thereafter. -/
structure Course (q : h≤k) (hN : k≤N) (E δ : ℝ) (top : Bands (Ranks C h p) (C.path.rep N p k)) {m : ℕ} (hr : h≤m) (hm : m≤k)
    (D : Stepwise.Foci (Ranks C h p) G (C.side m p)) (g : Hot (Ranks C h p)→ℝ) : Prop where
  spots : Multi.Afield (C.path.rep N p m).p (money C.path.levels m) (anchor C.S p hr) D g (Planning.width C δ m k E)
  saturation (i : System C h p) : Planning.width C δ m k E * g (Hot.one (Ranks C h p) i)=1/8
  resolves (s : (Ranks C h p).Mode) : (fun U => (Multi.many (C.path.rep N p m) (Ranks C h p) D U).part s)=wave B v q hN hm s
  fires (x : System C h p) : m<k → D (Hot.one (Ranks C h p) x)= keyed B v hr x
  inlet : (e : m=k) → HEq D (Compile.rolls top)



/-- Per m remaining geometry/numerics. Rooms only for eventually stamping
receipts at stops. Purchased WITHOUT deciding N or any representations. -/
structure Legal (C : Family G) (d m p : ℕ) (δ : ℝ) {h : ℕ} (hm : h≤m) : Prop where
  constellation : Multi.Spot (C.path.levels.budget m)
  aperture : Multi.Maquette.room (C.localSection d) ≤ C.path.levels.clock.coverSize m
  spaced : Spaced (anchor C.S p hm) (C.path.levels.clock.coverSize m)
  shifts : Planning.Quotes C δ m d

variable {B v} (H : C.Makes) (hB : B.Based C.params (C.localSection d) (C.ref d))
    {q : h≤k} {hN : k≤N} {E δ : ℝ} {T : Bands (Ranks C h p) (C.path.rep N p k)}
    {W : Worth}
    {fee : System C h p → ℕ → ℝ}
    (hδ : 0≤δ) (he : roomCost C.path.levels W) (hb : Bank W C.path.levels)
    (hRec : ∀ x : System C h p, Pair.Recovery B (Pair.spin C v x) (fee x) W δ)

include H hB he hb hRec hδ


variable (hpos : 0 < E) {R : ℝ} (hE : Pair.principal C k R ≤ E)
    (hR : ∀ x : System C h p,(C.labels.level d).coeffSize (Pair.spin C v x) ≤ R)
include hpos hE hR


end YM.AnalyticNext.GridStop
