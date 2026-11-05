import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import YM.Extra.ITERATION_NO_LOSS.Local
import YM.Extra.ITERATION_NO_LOSS.Spectrum
import YM.Extra.MULTISOURCE_BOUNDS.Application
import YM.Extra.MULTISOURCE_BOUNDS.Germs
import YM.Extra.SOURCE_HISTORIES.Issue
import YM.Extra.SOURCE_HISTORIES.PaddedBolt
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Timetable
import YM.Next.ROTATIONS.Switch
import YM.Progress.DIRECTED_RECIPE.Rollout
import YM.Push.CUTOFF_PROJECTORS.Along



/-!
# Cook into an exact history and family C

This specialization uses program analytic inputs on a single future-chosen
replay Gates with G still physical and Levels funded once. Use it e.g.
inside the after-awards callbacks (`Requisitions`). These quantities
 and Hertz prices still have to be proven as *actual* analytic estimates
and transfers on the SAME bake. β & path and choices are already fixed.
`Program`, `Stays`, Oust, and the precursor Calendar sufficiency hypotheses
like numerical reclosure are not demanded from physics. Normalize Client
labels coherently via Issue on a jolt with TRUE Shelf. Extra.Multi gets the
repainted stronger top price from Crisis helper even despite jolt, before
querying those arrays. -/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Cook
open Set Filter Function MeasureTheory Lattice RG Supply Pressure Precision
  Extra Extra.Iteration WilsonStartup Labels Source Wilson Input Org Spec
  YM.Further.PhysicalPeriodLimitF933.Timing Next.Foundations Extra.Histories
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {κ : ℝ} {hκ : 0 < κ} {J : PhysicalPeriodLimitF933.Timing.OrderBook}
  {M : PhysicalPeriodLimitF933.Timing.Inception G κ hκ J} {R : PhysicalPeriodLimitF933.Timing.Requests}
  {S : PhysicalPeriodLimitF933.Timing.Layout M R} {V : PhysicalPeriodLimitF933.Timing.Reserves} {L : PhysicalPeriodLimitF933.Timing.Ledger M S V} {n : ℕ → ℕ} {β : ℕ → ℝ}
  {D : Rolls {L.s with floorL:=n}}
  {B : PhysicalPeriodLimitF933.Timing.Increments D} {power : ℝ} {T : Protection D} {X Y : Supply.Delays T} {Z : Bar Y} {U : Wait Z}
open Push.Corrected renaming Prices → CorrFees
variable (h : G.Simple)
variable {P : PhysicalPeriodLimitF933.Timing.Price D}

private abbrev I := Push.Corrected.Zone.Coverage.seats (Y:=Z) h U

/-- Use the SAME S.O quote. Gates chosen for the final Plan. -/
abbrev chief {a : Levels G} {H : Horizon a} {g : Kin H (chart G)} (r : PhysicalPeriodLimitF933.Timing.Rail M S L (β:=β) B X Y power) (pay : Paid (I (U:=U) h) a)
    (he : H.Suffices S.O) (ha : g.Planned (PhysicalPeriodLimitF933.Timing.ceiling P B)) (V : Builder.Gates a) :=
  { post := ceiling P B
    θ := T
    delay := Y
    bar := Z
    asks := I h
    prices := r.stock
    B := Builder.assign pay (chart_ok G) he ha V : Alloy
      (M:=by exact {p:={L.s with floorL:=n},K:=S.O,O:=chart G,oga:=chart_ok G}) D }

/-- Kneads needs the fresh dynamical
port `Rates` at this deployed H, through exact period and τ stationarity
and independent-width/cap powers (`Writer` at coarse Mode may be used to
prove it), all from the bought R.

Then ask Quests of the revised unmasked
planner.

The path revision is NOT just a different cutoff: keep receipts
and stations, moves of one F'.

Through-path costs can use the same S.O
Ringing.

Satisfaction of THESE antecedents under preceding price choices
not asserted here!

B.World quantities might have to charge a still stronger
worksheet simultaneously; pursue support compatibility ahead of application. -/
structure Ingredient {a : Levels G} {Q C : Horizon a} (d : PhysicalPeriodLimitF933.Timing.Deployed (L:=L) U h a Q C) (r : PhysicalPeriodLimitF933.Timing.Rail M S L (β:=β) B X Y power)
    (P : PhysicalPeriodLimitF933.Timing.Price D) : Prop where
  /-- No unpriced planner promise. Critical and FiniteBound themselves
  are not here, check exact Rates; major red L-loop and classical lift
  gates. -/
  fresh : Extra.Iteration.Rates Q M.K R.U R.A R.H (PhysicalPeriodLimitF933.Timing.ceiling P B) (chart G)
  retain (T' : Horizon a) (f : Kin Q (chart G)) (g : Kin T' (chart G)) (hF : Launched U h f (PhysicalPeriodLimitF933.Timing.ceiling P B) T' g) :
    ∃ F₀ : Builder.Gates a, F₀.Pass ∧ Rebuild.Actual (chief h r d.run hF.credit hF.finalPlan F₀).B V.census B.fuel

variable {a : Levels G} {Q C : Horizon a} {d : Deployed (L:=L) U h a Q C} {r : Rail M S L (β:=β) B X Y power}
variable {h}



variable {hG : G.Simple}
variable (K : Alloy (M:={ p := {L.s with floorL:=n}, K := S.O, O:=chart G, oga:=chart_ok G }) D) (b : Bolt K)

/-- `ω` thicker candidate path in preparation for all later calls. -/
abbrev start := Extra.Histories.Pads.jolt K b
abbrev closedTrail := Issue.trail (start K b)

variable {K}
lemma rise (H1 : ∀ N, Crisis.Early K.B.a N)
  (hc : ∀ N p, let H := Issue.trail b
               H.rep N p N=Start.layout K.B.a N p (H.β N p N)) :
    ∀ {params labels D ref factory}, ∀ N p : ℕ, Extra.Multi.Thick (Family.mk (closedTrail K b) params labels D ref factory) N p := by
  intro params labels D' ref f N p
  let C := ({ path := closedTrail K b, params := params, labels := labels, localSection := D', ref:=ref, factory:=f } : Family G)
  apply Crisis.pad_thick (C:=C) (H1 N)
  · exact (congr_arg Extra.Histories.Pads.bulk (hc N p))
  exact ((start K b).choice.represents N p N le_rfl).band

-- now entire first ingredient in exact orders

structure Backstory (a : Levels G) where
  K : Alloy (M := {p := {L.s with floorL:=n}, K:=S.O,O:=chart G, oga:=chart_ok G}) D
  V : Bolt K
  level : (Issue.trail V).levels=a

abbrev references (u : Backstory (L:=L) (D:=D) a) : ℕ→ℕ := Issue.choose_reference (Issue.trail u.V).levels |>.choose
abbrev topShelf (u : Backstory (L:=L) (D:=D) a) : ∀ N p, Shelf ((closedTrail u.K u.V).rep N p N).activities :=
    fun _ _ => Extra.Histories.Pads.supplies _

abbrev family (u : Backstory (L:=L) (D:=D) a) (T : (d N p : ℕ) → TransferData ((frames G).level d) (closedTrail u.K u.V) N p) :=
  Family.mk (closedTrail u.K u.V) (hol G) (frames G) (localSection G) (references u) T

structure Raw (h : G.Simple) {a : Levels G} (u : Backstory (L:=L) (D:=D) a) (r : Rail M S L (β:=β) B X Y power) : Prop where
  approves N p : let H := Issue.trail u.V; H.rep N p N=Start.layout u.K.B.a N p (H.β N p N)
  usable : Paid (I (U:=U) h) a -- implicit U not deduced from r? field U omitted if unspecified
  pages : Extra.Histories.Doors.Budget a V.source L.W

structure Readies (h : G.Simple) (U : Wait Z) (u : Backstory (L:=L) (D:=D) a) (F : (d N p : ℕ) → TransferData ((frames G).level d) (closedTrail u.K u.V) N p)
    (r : Rail M S L (β:=β) B X Y power) (e : Raw (U:=U) h u r) : Prop where
  printed : Issue.Printed (closedTrail u.K u.V) L.W V.source (topShelf u) (references u) F
  calibrated : Spec.Calibrated (family u F)
  history : Org.Assembly (Extra.Histories.Pads.jolt u.K u.V) (family u F)
  serial : (family u F).path.levels=a
  center (g : Extraction.Order) : Extraction.CenterPort (family u F) g
  offer : Extra.Multi.Offer (family u F) B.multi
  prepared : Extra.Multi.Prepared V.sectors B.multi (localSection G) a
  occupied : ∀ N p, Extra.Multi.Thick (family u F) N p

structure Ingredients (h : G.Simple) (U : Wait Z) (u : Backstory (L:=L) (D:=D) a) (r : Rail M S L (β:=β) B X Y power)
    (e : Raw (U:=U) h u r) : Prop where
  atom : Issue.PerBlock (closedTrail u.K u.V) V.source (references u)
  source (T : _) (H : Issue.Printed (closedTrail u.K u.V) L.W V.source (topShelf u) (references u) T) :
    ((∀ N p, Extra.Multi.Thick (family u T) N p) → Extra.Multi.Offer (family u T) B.multi)

variable (h)
lemma assemble (U : Wait Z) (u : Backstory (L:=L) (D:=D) a) (r : Rail M S L (β:=β) B X Y power)
    (e : Raw (U:=U) h u r) (hE : Ingredients h U u r e) : ∃ F, Readies h U u F r e := by
  let z := start u.K u.V
  have hz : (Issue.trail z).levels=a := u.level
  obtain ⟨F,hF,K⟩ := Issue.bolt L.W V.source (references u) z (show Extra.Histories.Doors.Budget (Issue.trail z).levels V.source L.W from (congr_arg (fun x => Doors.Budget x V.source L.W) hz.symm).mp e.pages) (topShelf u)
    (Issue.choose_reference _).choose_spec hE.atom
  let C := family u F
  have hf : Extra.Multi.Prepared V.sectors B.multi (localSection G) a := r.many _ _ _ e.usable
  have ht : ∀ N p, Extra.Multi.Thick C N p := rise u.V (fun N => by rw [show u.K.B.a=a from u.level]; exact Crisis.paid e.usable r.strengthened h N) e.approves
  have hh := hE.source F hF ht
  refine ⟨F,hF,K,⟨rfl, Extra.Multi.metered h hF.issued (s:=V.sectors) ?_ (Eventually.of_forall ht) hh⟩,hz,fun f => (Extra.Multi.centered h hF.issued (s:=V.sectors) ?_ (Eventually.of_forall ht) hh).2 f |>.1,
    hh,hf,ht⟩
  all_goals
    change Extra.Multi.Prepared V.sectors B.multi (localSection G) (Issue.trail z).levels
    exact (congr_arg (fun a => Extra.Multi.Prepared V.sectors B.multi (localSection G) a) hz.symm).mp hf
end YM.Further.PhysicalPeriodLimitF933.Cook
