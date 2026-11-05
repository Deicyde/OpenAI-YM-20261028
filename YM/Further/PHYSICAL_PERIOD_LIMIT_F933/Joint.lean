import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WEAK_SCALING_ACTLAW.Rooted
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Billing
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.CoupledShell
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Cuisine
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.GridIncome
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.OrderedBooks
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.SignedCoins
import YM.Next.MAXWELL.Det
import YM.Next.MAXWELL.Lit
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.COMMON_WITNESSES.Early
import YM.Push.CORRECTED_COLUMNS.Recruit
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Dollar
import YM.Push.STATIONARY_UNIFORM.Cost
import YM.Push.STRESS_FLUX.FreeBridge
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Campaign






/-!
# Common cutoff financial contract at the b70 Family

A fixed C, restart conventions etc from `Cook`.

Work at even any r s T of our meeting, so can be accessed
 after refining for Snap/Ranks or prove uniformly upstream if possible;
 don't fit a new gauge calendar after using a port.

Need only Promo for
 one extraction order for CP, for-pay tasks outside that scope might need
 more.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Joint
open Function Filter MeasureTheory Lattice RG Supply Wilson Labels Source Cells
  Input Spec Org Extraction Dash Climb Table Next.Extract Push.CutoffProjectors
  Extra.Histories Push.Common Snap Push.Corrected UVNext.Grade
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {C : Family G}
variable {κ : ℝ} {hκ : 0 < κ} {J : PhysicalPeriodLimitF933.Timing.OrderBook}
  {M : PhysicalPeriodLimitF933.Timing.Inception G κ hκ J} {U : PhysicalPeriodLimitF933.Timing.Requests}
  {S : PhysicalPeriodLimitF933.Timing.Layout M U} {V : PhysicalPeriodLimitF933.Timing.Reserves} {L : PhysicalPeriodLimitF933.Timing.Ledger M S V} {n : ℕ → ℕ} {β : ℕ → ℝ}
  {D : Rolls {L.s with floorL:=n}}
  {B : PhysicalPeriodLimitF933.Timing.Increments D} {power : ℝ} {T : Protection D} {X Y₀ : RG.Supply.Delays T} {Z : Bar Y₀} {w : Wait Z}
  {a : Levels G} {h : G.Simple} {b : Cook.Backstory (D:=D) a}
  {r : PhysicalPeriodLimitF933.Timing.Rail M S L (β:=β) B X Y₀ power} {c : Cook.Raw (U:=w) h b r}
  {F : (d N p : ℕ) → TransferData ((frames G).level d) (Cook.closedTrail b.K b.V) N p}
open Push.Common renaming Slot → CellSlot

/-- Fix one MaxwellData *produced*. Including the exact normalization
and Γ κ/vacuum convention of B70FurtherConnections (that theorem
leaves κ and voyage out of its spec; choose via its procedure). -/
structure Comparator (C : Family G) where
  a : FreeInput C
  vac : a.reads.vacuum=Maxwell.Free.voyage C.labels
  shift : a.T.κ=(Maxwell.Free.herald C.book 1 one_ne_zero).κ
  tilt : a.T.W=(Maxwell.Free.herald C.book 1 one_ne_zero).W
  realJ : ∃ τ : ℝ, τ ≠ 0 ∧ a.T.J= τ • StressFlux.material (Climb.Bel C.book) StressFlux.weyl
  freeD : a.Divergence

theorem comparator (h : G.Simple) (C : Family G) : Nonempty (Comparator C) := by
  obtain ⟨M,hM,hV⟩ := Maxwell.Free.maxwell_supplies C h 1 one_ne_zero
  obtain ⟨P,hκ,hW,hK,hv,he⟩ := StressFlux.FreeBridge.calibrate h M
  let X : FreeInput C := ⟨P.T,P.hT,P.lit,P.frames⟩
  have hx : X.reads=P := FreeInput.reads_spin_eq P
  obtain ⟨τ,hT,hr⟩ := he
  exact ⟨⟨X,hx.symm ▸ hv.trans hV,hκ.trans (congr_arg (fun T : Lighthouse C.book => T.κ) hM), hW.trans (congr_arg (fun T : Lighthouse C.book => T.W) hM),⟨τ,hT,hr⟩,
    bills_free h X τ hr⟩⟩

variable (C)
abbrev phantom : Table C.book := ⟨fun _ _ => 0⟩ -- structure `value`

-- use ANY input table for free (phantom S); doesn't ask it satisfies Base
variable {C} {e : Extraction.Order} (Y : Comparator C)

abbrev basic (d : ℕ) := Recruit.basis (phantom C) Y.a.kernels.spin
  (Bel.viaAll Y.a.kernels.positive (0:Axis)) d

/-- Stronger reading of the W-level request `Recruit.Makes` from the
companion CorrWork. For each actual supported comparison *geometry*
on the chosen sequence (can specialize to one builder presenting a
B first), need Tune/mark budgets. `Survey.Ready`, convergence to Base,
Count etc not assumed here. The choice of w.r.t. pressure Increments
before selecting history/Order must allow all d and k, same F.
-/
structure Presents (C : Family G) {q : RG.Supply.Sheet G} {D : Rolls q} (I : PhysicalPeriodLimitF933.Timing.Increments D) (Y : Comparator C) (e : Extraction.Order) where
  γ : ℝ
  couples : I.e < γ
  extent : ℕ → ℝ
  pos d : 0 < extent d
  activate d (A : Series C) : A.b=extent d → Placed (basic Y d) A → C.ref d ≤ A.depth 0 →
    ∃ T : Push.Corrected.Tests (basic Y d), T.B=A ∧
      (∀ k, ∃ X : ℝ,0 ≤ X ∧ ∀ p, ∀ᶠ i : ℕ in atTop, ∀ j, ‖T.tune k (e.mesh i) p j‖ ≤ X) ∧
      ∀ k, e.late fun N p => ∃ B : Wire C (A.side k) (A.depth k) N p,
        ∃ hB : T.B=A, Flow.Crew T k N p (hB ▸ B) (I.α (C.path.levels.clock.J (A.side k))) (C.path.levels.clock.monitor (A.depth k)^γ)
-- alternate weaker precise assumption sufficient; geometry/chamber furnishing
-- theorem won't directly pay geometry fields not charged on that path; this
-- is useful when physics suppliers have to choose more paid Works at k (e.g.
-- λ balances through more ancestors) than just `Placed`. Availability is
-- a supplier assumption, so might ask Nonempty Kit on THOSE curves.
structure Pack {q : RG.Supply.Sheet G} {D : Rolls q} (I : PhysicalPeriodLimitF933.Timing.Increments D) (Y : Comparator C) (e : Extraction.Order) where
  γ : ℝ
  couples : I.e < γ
  extent : ℕ → ℝ
  offer d : Recruit.Makes (phantom C) Y.a.kernels.spin (Bel.viaAll Y.a.kernels.positive (0:Axis)) d e I.α γ (extent d)



/-- Basis weak cost plan. All at C at this e. Request on arbitrary Seed
and orders per further clients; intended to be supplied from estimates
on the hierarchy already inherited by the chosen Seed (or **purely
finite** w.r.t. C *uniformly* on all these orders), with Sector/H
incomes for ROOTED polynomials (or the aligned point estimates in
`Alloc`), including sup price at centered h grid and admission across
projection ties. These aren't estimates on S. This version reserves the
same normalized free basis as recruitment (and spin), not requiring an
Iso receipt or discrepancy matrix on b. -/
structure Catalogue (Y : Comparator C) (e : Extraction.Order) : Prop where
  funding (M D : ℕ) (Q : ℝ) : 1 ≤ Q → ∃ (u : Extraction.Order) (b : Extra.WeakScaling.Stations C),
    let f := e.refine u
    (∀ k d, ∃ A : ℝ, 0 ≤ A ∧ ∃ p₀ : ℕ, ∀ p ≥ p₀, ∀ᶠ j in atTop, ‖b.coef k d (f.mesh j) p‖ ≤ A) ∧
    (∀ k d, d≤D → Extra.WeakScaling.Sym b f Y.a.kernels.spin k d) ∧
    Extra.WeakScaling.BasisCenter b f (fun d => (basic Y d).basis) M D Q ∧
    (Extra.WeakScaling.RootCosts b f (fun d => (basic Y d).basis) M D Q ∨ Extra.WeakScaling.AlignedCosts b f M D Q)

lemma Catalogue.scheduled (hC : C.Makes) (H : Catalogue Y e) : Extra.WeakScaling.Supply C e Y.a.kernels.spin := by
  intro M D Q hQ
  obtain ⟨u,b,h,hE,hc,hb|hb⟩ := H.funding M D Q hQ
  · exact ⟨_,_,Extra.WeakScaling.finite_of_basis hC (by linarith) h hE hc hb⟩
  exact ⟨_,_,h,hE,Extra.WeakScaling.center_of_basis hC hE hc,hb⟩

/-- Geometric width variant explicitly needs the common-h estimates for
**any** already procured p:f.refine g below the needed order. Can pay
Ancestor style estimates for all w with actual labels/stress algebra, not
post hoc choices of axial sign. Only one of the possible ways to commission
the towers at this point. -/
structure ByNode (T : Table C.book) (W : DiffPlan T) (e : Extraction.Order) : Prop where
  fees (w : StressFlux.Coeff) : ‖w‖=1 → StressFlux.nabla W (StressFlux.material T w)=0 → StressFlux.Centers (StressFlux.material T w) →
    OnDemand e fun (l : Leg T) r => 4 ≤ l.1 → ∃ B : C.label l.1,
      T.project _ B = UVNext.Grade.spectrum _ l.1 l.2.2 ∧
      Shell.PaidNode r (StressFlux.token C w) B (payLevel l.1 l.2.1) (shellWeight l.2.1)

structure Collaborations (Y : Comparator C) {b : Presentation C} {w : Snap C} {u : Upper w}
    {Q : Guests u.T} (p : Hosted u b Q e) : Prop where
  weak : Catalogue Y e
  shells (g : Extraction.Order) : Next.UVStress.Stations C (e.refine g) Y.a.kernels.spin →
    (∃ J : u.T.Stress, J ∈ Next.UVStress.KernelSpace p.seed.kernel.spin ∧ J≠0 ∧ Conserved u.V p.seed.kernel.spin J) →
    ByNode u.T u.V (e.refine g)

variable {R₀ : Presentation C} {s : Snap C} {u : Upper s} {q : Guests u.T}

lemma plays (p : Hosted u R₀ q e) (H : Collaborations Y p) : WeakStock C Y.a.kernels.spin e ∧
    ∀ g, Next.UVStress.Stations C (e.refine g) Y.a.kernels.spin →
      (∃ J : u.T.Stress, J ∈ Next.UVStress.KernelSpace p.seed.kernel.spin ∧ J≠0 ∧ Conserved u.V p.seed.kernel.spin J) →
      G.Simple → ProbeOffer (e.refine g) p.seed.kernel u.V := by
  have hw := UVNext.Grade.stations_paid
    (show Next.UVStress.Stations C e Y.a.kernels.spin from
      Upload.fair p.seed Y.a.reads p.atBase.base.clean.ready p.atBase.base.clean.tilt (H.weak.scheduled Y p.seed.cutoff))
  refine ⟨hw,fun g hg hv hG => ?_⟩
  have ht := p.upon (Tails.refine e g)
  obtain ⟨Z,hZ,X⟩ := Next.UVStress.Stations.equivalences p.seed.kernel ht.seed.ordered Y.a.kernels hg
    ht.atBase.base.clean.ready (V:=Y.a.T.W) ht.atBase.base.oriented Y.a.lit.edges Y.a.lit.hers
    (Next.UVStress.cap_given ht.seed.corrected)
  obtain ⟨k,h4,h5⟩ := ((X.hsym 4).and (X.hsym 5)).exists
  have hb : Countable (Leg u.T) := by unfold Leg Orbits; infer_instance
  apply Shell.leg_offers Y.a p.seed.kernel p.atBase.base.oriented (Z.U k 4) (Z.U k 5) h4 h5 hG p.seed.cutoff ht.atBase.base.center
  intro w hw hn ht
  apply OnDemand.stations
  intro l r
  obtain ⟨s,h⟩ := (H.shells g hg hv).fees w hw hn ht l r
  refine ⟨s,fun h' => ?_⟩
  obtain ⟨X,hX,H⟩ := h h'
  exact ⟨X,hX,H.broad⟩

-- final prospects are conditional on already filling C receipts (enables
-- other concurrent branches to adopt without retuning). This choice requires
-- later demands even across orders where Risen exists with SOME other
-- comparison path. In the physical implementation might prove only along
-- explicitly serving `Guests` which seek their C -- then can use our
-- alternate continuation with Fixed Jobs. No assumption of their existence
-- is needed to say this interface.
structure Estimates (C : Family G) {s : RG.Supply.Sheet G} {D : Rolls s} (V : PhysicalPeriodLimitF933.Timing.Increments D) (W : Bid.Worth)
    (Y : Comparator C) (A : Campaign C) (t : Extraction.Order) where
  erase (d : ℕ) : ∃ P : Equations.Sheet A d, Equations.Invoices A d P t W
  rank (d : ℕ) : Module.finrank ℂ (Maxwell.equationIdeal G d) ≠ 0 →
    ∃ M : ProjectorNext.Calibration.Machine C.params d,
      (t.late fun N p => ProjectorNext.Calibration.Wears A M N p) ∨
       (t.late fun N p => M.Rain A N p)
  corrected : Pack V Y t
  grill {w : Snap C} (u : Upper w) (g : Extraction.Order) : Risen u A.presentation (t.refine g) → Push.GridApprox.AtMaterials C (t.refine g) u.T
  endgame {w : Snap C} (u : Upper w) (Q : Guests u.T) (g : Extraction.Order) (H : Hosted u A.presentation Q (t.refine g)) : Collaborations Y H

-- this partial spending also leaves direct base/holder data for the efficient continuation
structure Coupons {A : Campaign C} (Y : Comparator C) (e : Extraction.Order) : Type _ where
  π : Push.Corrected.Survey C (phantom C)
  probes : π.X=basic Y
  center : CenterPort C e
  billed i : RelayCosts A.presentation e i
  amount i : Persist.Count A.presentation e i
  paid i : (π.Y i).Offer (π.price i) e
  works i : ∃ c > (0:ℝ), e.late (Billing.Works A i c)

variable {Y} {A : Campaign C}
lemma inventory (h : G.Simple) (q : Estimates C B L.W Y A e)
    (hp : Bid.Bank L.W C.path.levels) (hh : Bid.roomCost C.path.levels L.W)
    (ht : Paid w C.path.levels) (r : PhysicalPeriodLimitF933.Timing.Rail M S L (β:=β) B X Y₀ power)
    (hP : CenterPort C e) : Nonempty (Coupons (A:=A) Y e) := by
  let shop : Push.RelayDifference.Shop C L.W := ⟨h,A.cutoff,Stock.consumes ht r.stock,hh,hp⟩
  choose P hE using q.erase
  have hm (i : ℕ) : Billing.Banked A i e L.W := ⟨fun HI =>
    ⟨(hE i).paper.mono (fun _ hl => hl.mono fun _ he => he.compares), q.rank i HI⟩⟩
  obtain ⟨c,hc,hC,hD⟩ := Billing.Banked.receipts hm hp hh shop.simple
  obtain ⟨π,hπ,-,hπ'⟩ := Push.Corrected.Recruit.together h (Joint.phantom C) Y.a.kernels.spin (Push.Corrected.Bel.viaAll Y.a.kernels.positive (0:Axis))
    ht B.pos q.corrected.couples r.finalPage (fun j => B.cash j) q.corrected.offer
  exact ⟨π,hπ,hP,fun i => Push.RelayDifference.finite_relay shop (Equations.Invoices.purchased A (P i) hp hh (hE i)),hD,hπ',fun i => ⟨_,hc i,hC i⟩⟩

lemma roll {Y : Comparator C} (H : Coupons (A:=A) Y e) (h : G.Simple) (Hc : Calibrated C)
    (E : Estimates C B L.W Y A e) : UVNext.Grade.Recorder C A.presentation e where
  active := A.cutoff
  calibrated := Hc
  center := H.center
  fee := A.costs _
  after_snap g _ h₁ := Billing.detective H.π h (H.π.tail (Tails.refine e g) H.paid)
    (fun i => Persist.further (H.amount i) (Tails.refine e g))
    (fun i => (Tails.refine e g).relay (H.billed i)) h₁
  rank g _ _ p := Billing.stock H.π h (H.π.tail (Tails.refine e g) H.paid) (fun i => Persist.further (H.amount i) (Tails.refine e g)) p
  grid g _ u X hR HX := PhysicalPeriodLimitF933.Grid.ready (E.grill u g hR) Extraction.Order.full hR X HX
  approaches g _ u _ p q hx := ⟨Y.a,Y.freeD,(plays Y hx (E.endgame u q (g.refine p) hx)).1,fun j ht hT => (plays Y hx (E.endgame u q (g.refine p) hx)).2 j ht hT h⟩


end YM.Further.PhysicalPeriodLimitF933.Joint
