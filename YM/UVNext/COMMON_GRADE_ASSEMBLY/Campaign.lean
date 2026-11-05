import YM.UVNext.COMMON_GRADE_ASSEMBLY.Coordinates
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Stage
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Tables

/-!
# The revised producer contract

Every physical
figure incl all-period CenterPort, history labels, Armed Occupancy (if using
Metered etc) still has to be bought at the schedule chosen.

Estimates of
actual likelihood, remainder & marked sector inputs NOT priced in this work;
we simply begin with C, Makes and Calibrated and ask for the listed financial
bills at their stages (OR supply them uniformly earlier, compare Instruments).

No claim of their feasibility/recentering/scalar normalizations.

No
renormalization of C.path by changing periods after producing C.

No claim
of `Next.BOUNDARY.Producers`: that retains large parameter goals about YU
in addition which might be too strong and aren't needed in the downstream
consumers used here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.Grade
open Set Function Filter MeasureTheory Analysis Extraction Table Ward Climb Org Spec Lattice Wilson Cells
  Next.Extract Next.UVStress Push.Common Snap Push.CutoffProjectors Dash
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {C : Family G} {f g : Extraction.Order} {b : Presentation C}

/-- Cutoff demands at an early Order. `calibrated` and `active` are on the
whole C before extraction (important!); often arrive via Assembly from even
more commitments (Program etc, Metered, pricing across all calls uniformly at
pre/post L). `grid` may for instance be served by Common.Study (or see
`grill_served` for a Furnace already paid), but charge it only once no matter
which. `rank` may for instance be served from equation projectors/Offers
without an independent size input (`projector_clocks`). `approaches` can ask
for success *after* everything else at the inherited Orders; then still keeps
the Base tables & phase appointments while arranging further receipts. Does
NOT ask for Climb.Pre, ActLaw or assume Grill, BOUNDARY lifts, Grades, Final,
selection physics, etc. Nor any existence of `Stock`/Sustained/Convergence
at one COMMON final refinement through some other shortcut. See AfterHost
(free inputs normative, divergence type, station and priced shell calls).
-/
structure Recorder (C : Family G) (b : Presentation C) (f : Extraction.Order) : Prop where
  active : C.Makes
  calibrated : Calibrated C
  center : CenterPort C f
  fee : Affordable b f
  after_snap (g : Extraction.Order) (w : Snap C) : First w b (f.refine g) →
    Stationed (f.refine g) (fun d r => RelayCosts b r d ∧ Detector b r d)
  rank (g : Extraction.Order) (w : Snap C) (u : Upper w) : Risen u b (f.refine g) →
    Push.Common.Stock b u.T (f.refine g)
  grid (g : Extraction.Order) (w : Snap C) (u : Upper w) (D : Holder u.T) : Risen u b (f.refine g) → D.Income b (f.refine g) →
    GrillInputs C (f.refine g)
  approaches (g : Extraction.Order) (w : Snap C) (u : Upper w) : Risen u b (f.refine g) → AfterHost u b (f.refine g)







/-- Usable pricing-oriented version. E.g. if providing from projectors,
choosing geometry & free lighting already from some earlier S (or any
Table, see `transfer`), and Grill via centred single-field, all at same
raw C. Even split relay and Detector demands into compatible OnDemand
calls since Tails transfer available. Not requiring either *all at one g*
or one after-the-grades setup phase. In this version request arbitrary
inherited service and hence persistent invoices rather than arrange specific
towers (compare Recorder). Campaign Compares style arguments and Woke,
weak comparisons etc implementing these hypotheses remain large open
requests. -/
structure Instruments {T : Table C.book} (A : Campaign C) (X : Offers T) (a : FreeInput C) (f : Extraction.Order) : Prop where
  center : CenterPort C f
  relay : OnDemand f fun d u => RelayCosts A.presentation u d
  search : OnDemand f fun d u => Detector A.presentation u d
  -- No separate fee/d-upper estimate IF injective at physical cutoff &
  -- RFREE residual problem solved. Use `Cardinal` (outer period threshold
  -- before eventual mesh), not necessarily all cutoffs.
  at_cut : Cardinal A f
  freeInputs : (∀ d, Maxwell.residual G d = ⊥) ∧ a.Divergence
  estimates : EarlyRank X f
  heat : Study C f
  -- weak estimates here already *persistent*, can be ordered earlier or later.
  base : OnDemand f (WeakBill C a.kernels.spin)
  -- need actual shell estimates whenever asked after entering compatible Base (Born)
  -- could postpone even further as in `AfterHost`. Supplies even conditional on
  -- the existence of centered nonzero current as in main campaign; use
  -- ProbeDemand (can buy m,y estimates on finer stations).
  asks : ∀ g (w : Snap C) (u : Upper w) (H : Risen u A.presentation (f.refine g)),
    (∃ J : u.T.Stress, J ∈ KernelSpace H.base.kernel.spin ∧ J≠0 ∧ Conserved u.V H.base.kernel.spin J) →
    ProbeDemand (f.refine g) H.base.kernel u.V

private lemma owns {ι : Type*} [Countable ι] {P U : ι → Extraction.Order → Prop} (h : OnDemand f P)
    (p : OnDemand f U) (H : ∀ i b c,Tails c b → P i b → P i c) : Stationed f fun i u => P i u ∧ U i u := by
  apply OnDemand.stations; intro i k
  obtain ⟨x,hx⟩ := h i k
  obtain ⟨y,hy⟩ := p i (k.refine x)
  exact ⟨x.refine y,H _ _ _ (Tails.refine ((f.refine k).refine x) y) hx,hy⟩

theorem projector_clocks {T : Table C.book} (A : Campaign C) (X : Offers T) (a : FreeInput C)
    (h : Instruments A X a f) (hc : Calibrated C) : Recorder C A.presentation f where
  active := A.cutoff
  calibrated := hc
  center := h.center
  fee := A.costs f
  after_snap _g _w _p := owns (demand_persists h.relay (Tails.refine ..))
    (demand_persists h.search (Tails.refine ..)) (fun _ _ _ t e => t.relay e)
  rank _g _w _u p := h.estimates.jobs p (Tails.refine ..)
    (Cardinal.comparison A (h.at_cut.persists (Tails.refine ..)) p h.freeInputs.1)
  grid _g _w _u _D p _ := charges_grid h.heat p (Tails.refine ..)
  approaches g w u p := posts a h.freeInputs.2 p.base.kernel ⟨demand_persists h.base (Tails.refine ..),h.asks g w u p⟩ _





end YM.UVNext.Grade
