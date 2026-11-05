import YM.Extra.ITERATION_NO_LOSS.Gates
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.ITERATION_NO_LOSS.Rebuild
import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Extra.WILSON_STARTUP.Builder
import YM.Extra.WILSON_STARTUP.MixPay
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Crisis
import YM.Next.BOUNDARY.Coordinates
import YM.Next.EXTRACTION.Basis
import YM.Next.FREE_KERNELS.Calendar
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.CORRECTED_COLUMNS.Reserve




/-!
# A common price activation for the conditional producer

199xx etc; docs/Budget. Here is an actual numerical
compatibility test; all displayed orders/stamps etc kept in application
on these types. This is NOT all scheduling burdens for Yang-Mills (e.g.
must establish the sufficiency of these scopes for Rates/through-step
and all later physical estimates on the chosen history, or revise the
proposal). In particular doesn't presume or assert simultaneity of
outputs from the speculative branches! The use positions after issuing
can still strengthen/adapt (take further max of thresholds, delays etc.)
in future applications, checking the done physics promises still work
for such inputs. This portion of the path pricing doesn't yet use a
particular positivity-contour choice to infer K pressure costs, but it
*does* pay even the verified EBare `Ringing` grant on our final K.
Use it civilly; it's for actual approved trees/field/recipe calls.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Timing
open Filter Set Function Lattice RG Supply Precision Pressure Labels Source
  Next.Foundations Next.Free Extra.Iteration Craft Bid WilsonStartup
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}

/-- Set the order list as needed BEFORE choosing L. -/
structure OrderBook where
  k : ℕ → ℕ
  pow : ℕ → ℕ
  width : ℕ → ℝ -- support exponent
  monotoneA : Monotone k
  monotoneB : Monotone pow
  monotoneC : Monotone width
  grown (j : ℕ) : 6 ≤ k j ∧ j ≤ k j ∧ 2 ≤ pow j ∧ j ≤ pow j ∧ 0 < width j

structure Inception (G : Gauge) (κ : ℝ) (hκ : 0 < κ) (J : OrderBook) where
  p : RG.Supply.Sheet G
  hp : p.kernel = Next.Foundations.kernel G κ hκ
  stages j : (p.profile j).order=J.k j ∧ (p.profile j).power=J.pow j ∧ (p.profile j).supportExponent=J.width j
  X : MapPrices -- first H (free)
  l : ℕ → ℝ
  γ : ℕ → ℝ
  b : ℕ → ℕ
  pledge : Catalog p.kernel X l γ b
  clip j : (p.profile j).clip.direct ≤ γ j ∧ (p.profile j).clip.direct ≤ 1
  tall j : b j ≤ p.floorL j
  K : MapPrices -- reserve map prices for Rates
  rollback (Q : RG.Supply.Sheet G) (e : Upgrade p Q) (a : Levels G) : a.clock.stage = Q.profile → a.clock.kernel=p.kernel →
    ∀ H : Horizon a, Rack a X H → ∃ C, Bid.Retained C H ∧ C.Suffices K



variable {κ : ℝ} {hκ : 0 < κ} {J : OrderBook} (M : Inception G κ hκ J)

structure Requests where
  U : Apertures
  A : ClassicalCosts
  H : QuantumCosts

/-- Stage layout even before the source history planner has seen all
pre-L requirements. Startup-compatible clip *on this very profile*.
`overlay` reserve has already been made before e.g. the columns buy.
-/
structure Layout (R : Requests) where
  s : Supply.Sheet G
  cost : Upgrade M.p s
  first : s.first=M.p.first
  fit : Extra.Iteration.Before s R.U R.A R.H M.K
  startup j : WilsonStartup.Design.Suitable G (s.profile j)
  grown j : (s.profile j).order=J.k j ∧ (s.profile j).power=J.pow j ∧ (s.profile j).supportExponent=J.width j
  higher : M.p.floorL ≤ s.floorL
  O : MapPrices -- startup overlay, chosen before purchasing density level AtomStep costs/columns
  overlay (a : Levels G) (ha : a.clock.stage=s.profile) (H : Horizon a) :
    H.Suffices M.K → ∃ Q : Horizon a,Q.Suffices O ∧ Change.Overlay Q H



variable {R : Requests} (S : Layout M R)



lemma Upgrade.chain {A B C : Supply.Sheet G} (h : Upgrade A B) (ht : Upgrade B C) : Upgrade A C := by
  obtain ⟨a,b,c,d,e,f,g,j⟩ := h
  obtain ⟨A,B,C,D,E,F,G,J⟩ := ht
  exact ⟨A.trans a,fun i => (B i).trans (b i),fun i => (C i).trans (c i),fun i => (d i).trans (D i),fun i => (e i).trans (E i),
    fun i => (f i).trans (F i),fun i => (g i).trans (G i),fun i => (j i).trans (J i)⟩

open Extra Extra.Histories
/-- Density history anticipations. `source` bound allocated before L
anticipating AtomStep (ε handoffs paid here; proofs need rates admissible
 even when taking approvals after implants). `scope`, sector exponents
and count envelopes all anticipated (multi t below after L). `up`
arbitrary other columns increases already anticipated, never boost from
fitted data. -/
structure Reserves where
  source : ℕ → ℝ
  source_ge i : 1 ≤ source i
  up : ℕ → ℝ
  census : Rebuild.Census
  sectors : Extra.Multi.Scope

structure Ledger (P : Reserves) where
  s : Supply.Sheet G
  cost : Upgrade S.s s
  higher : S.s.floorL ≤ s.floorL
  clip j : (s.profile j).clip=(S.s.profile j).clip
  paths j : (s.profile j).paths=(S.s.profile j).paths
  first : S.s.first=s.first
  fit : Extra.Iteration.Before s R.U R.A R.H M.K
  startup j : Design.Suitable G (s.profile j)
  grown j : (s.profile j).order=J.k j ∧ (s.profile j).power=J.pow j ∧ (s.profile j).supportExponent=J.width j
  W : Bid.Worth
  plans : Doors.Plans s P.source W
  factorial j : ((s.profile j).order.factorial:ℝ) ≤ (s.profile j).columns
  extra j : P.up j ≤ (s.profile j).columns



variable {V : Reserves} (L : Ledger M S V)

/-- Quotes pre-L. -/
structure Available (v : ℕ→ℕ) (β : ℕ→ℝ) : Prop where
  -- domain is {L.s with floorL := v}. `v` can always be made larger
  higher : M.p.floorL ≤ v
  earlier : L.s.floorL ≤ v
  remake : Rebuild.Open V.census {L.s with floorL:=v}
  history D (a : Levels G) : a.clock.factor=(D : Rolls {L.s with floorL:=v}).L → a.clock.stage=L.s.profile →
    (∀ m, β (a.clock.J (m+1)) ≤ a.clock.hatBeta m) → Doors.Budget a V.source L.W
  prices (D : Rolls {L.s with floorL:=v}) (tar : Extra.Multi.Tariff) (m : ℝ) : 0 ≤ m → ∀ T : Protection D, ∀ A : Supply.Delays T,
    ∃ B : Supply.Delays T,
      B.shells=A.shells ∧ B.growth=A.growth ∧ A.scaleEntry ≤ B.scaleEntry ∧ A.betaEntry ≤ B.betaEntry ∧
        ∃ Y : ℕ→ℕ→ℝ, Testing.Ringing S.O Y B ∧ (∀ i j,m ≤ Y i j) ∧
          ∀ (p : Bar B) (I : Wait p) (a : Levels G), Paid I a → Extra.Multi.Prepared V.sectors tar (localSection G) a

-- use Multi.pricing; afterwards need Stock.Priced W explicitly; method therein produces Stock.priced but not carried through statement: switch to raise_gates on existing pressure quote
lemma Ledger.support (h : G.Simple) : ∃ v : ℕ → ℕ, ∃ β : ℕ → ℝ, ∀ n : ℕ → ℕ, v ≤ n → Available M S L n β := by
  obtain ⟨i,hi⟩ := Rebuild.more V.census L.s
  obtain ⟨j,β,hj⟩ := Doors.afford L.s V.source L.W L.plans
  obtain ⟨k,hk⟩ := Extra.Multi.pricing V.sectors (localSection G) h L.s S.O L.factorial
  refine ⟨fun e => max (max (i e) (j e)) (k e),β,fun n he => ?_⟩
  have hI u := (le_max_left (i u) (j u)).trans ((le_max_left ..).trans (he u))
  obtain ⟨hL,hR⟩ := hi n hI
  refine ⟨?_,hL,hR,hj n (fun u => (le_max_right ..).trans ((le_max_left ..).trans (he u))),hk n (fun u => (le_max_right ..).trans (he u))⟩
  exact S.higher.trans (L.higher.trans hL)

/-- Fix η first while allowing both-loop & advance customers' other
postage to look at it. A revised g for final use with the Input.Directed
is fixed after strength of the corresponding Fuel. Use even for any t
Beta reserve requested at W; ring the employment budget for FINAL O
quote. -/
structure Increments {s : Supply.Sheet G} (D : Rolls s) where
  fuel : Rebuild.Fuel D
  gamma : ℕ → ℝ -- thermal prefactor
  distance : ℕ → ℝ
  positive i : 0 < gamma i
  active i : 0 < distance i
  multi : Extra.Multi.Tariff
  e : ℝ -- terminal `η`
  pos : 0 < e
  α : ℕ → ℝ
  cash j : 0 ≤ α j

variable {n : ℕ → ℕ} {β : ℕ → ℝ} {D : Rolls {L.s with floorL:= (n:ℕ→ℕ)}} (B : Increments D)
variable {η : ℕ → ℝ} (Q : PostCost D)
structure Rail {T : Protection D} (A Y : Supply.Delays T) (warmth : ℝ) : Prop where
  vintage : A.betaEntry ≤ Y.betaEntry
  scale : A.scaleEntry ≤ Y.scaleEntry
  shells : A.shells ≤ Y.shells
  growth : A.growth ≤ Y.growth
  wilson : WilsonStartup.Timing.funded (frames G) (localSection G) {L.s with floorL:=n} Y.betaEntry
  strengthened : Crisis.Equipped {L.s with floorL:=n} Y.betaEntry
  book : β ≤ Y.betaEntry -- Beta doors issued earlier
  stock : Stock.Priced Y
  lateStep : Extra.Iteration.Warm R.H Y
  recalc : Rebuild.Cool V.census B.fuel Y
  finalPage : Push.Corrected.Last.OnPage Y B.e 2 B.α
  ring : ∃ t : ℕ → ℕ → ℝ, Pressure.Testing.Ringing S.O t Y ∧ ∀ i j, warmth ≤ t i j
  many (Z : Bar Y) (I : Wait Z) (a : Levels G) : Paid I a → Extra.Multi.Prepared V.sectors B.multi (localSection G) a


variable {L B M S}
lemma Available.rails (hG : G.Simple) (A : Available M S L n β) (X : Increments D)
    (power : ℝ) (hp : 0 ≤ power) (T : Protection D) (Y : Supply.Delays T) : ∃ P : Supply.Delays T,
      Rail M S L (β:=β) X Y P power := by
  let q : Supply.Delays T := {Y with betaEntry := fun i => max (Y.betaEntry i) (β i) }
  let p' : Supply.Sheet G := { L.s with floorL:=n }
  have he i : (p'.profile i).clip.direct ≤ 1 := (L.startup i).direct
  obtain ⟨f,hf⟩ := Crisis.prebuy G p' fun i _ => he i
  obtain ⟨v,hv,hK⟩ := WilsonStartup.Timing.choose (frames G) (localSection G) q (fun i _ => he i)
  let q' : Supply.Delays T := { q with betaEntry := fun i => max (v i) (f i) }
  have hx : q.betaEntry ≤ q'.betaEntry := hv.trans (fun _ => le_max_left ..)
  obtain ⟨P,h₀,h₁,h₂,h₃,h₄⟩ := Stock.raises q' hG
  obtain ⟨E,h,hE1,hE2,hE3,hE4⟩ := Rebuild.prices X.fuel (Extra.Iteration.warmup R.H P) hG A.remake
  obtain ⟨F,hF,h₈,h₉,h₆,ht⟩ := Push.Corrected.Last.delay E 2 X.α X.pos
  obtain ⟨B,hB1,hB2,hB3,hB4,Y',hY,hP,hi⟩ := A.prices D X.multi power hp T F
  refine ⟨B,?_⟩
  have hY₁ : Y.betaEntry ≤ q.betaEntry := fun _ => le_max_left ..
  have H1 : F.betaEntry ≤ B.betaEntry := hB4
  have H2 : E.betaEntry ≤ B.betaEntry := le_trans hF H1
  have H3 : (Extra.Iteration.warmup R.H P).betaEntry ≤ B.betaEntry := hE3.trans H2
  have H4 : P.betaEntry ≤ B.betaEntry := le_trans (fun _ => le_max_left ..) H3
  have H5 : q'.betaEntry ≤ B.betaEntry := h₀.trans H4
  have H : (Extra.Iteration.warmup R.H P).shells = B.shells := by rw [← h,hB1,h₉]
  have He : Y.growth=B.growth := by change q'.growth = _; rw [h₃,hB2,h₆,hE1]; rfl
  have hf' : P.scaleEntry ≤ B.scaleEntry := by rw [h₈,hE2] at hB3; exact hB3
  refine ⟨hY₁.trans (hx.trans H5),h₁.trans hf',(h₂.le.trans (fun _ => le_max_left ..)).trans H.le,He.le,hK _ (le_trans (fun _ => le_max_left ..) H5),
    hf _ (le_trans (fun _ => le_max_right ..) H5),(show β ≤ q.betaEntry from fun _ => le_max_right ..).trans (hx.trans H5),
    ⟨fun i hi x hx => h₄.1 i hi x ((H4 i).trans hx), fun i hi y x hx hz => h₄.2 i hi y x hx ((hf' i y).trans hz)⟩,
    (Extra.Iteration.warmed R.H P).boost H3 H.le,hE4.raise H2,fun j x hx => ht j x ((H1 j).trans hx),⟨Y',hY,hP⟩,hi⟩

structure Price (D : Rolls {L.s with floorL:=n}) where
  gap : ℕ → ℝ
  positive j : 0 < gap j
  serves (Q : PostCost D) : Q.η=gap → Extra.Iteration.GapQuote D M.K Q



/-- The actual deployment on ANY such final bar, INCLUDING restarted
middle-stage estimates requiring `l/m_ref` seats. Doesn't commit to
picking just small U; can preanticipate further post-L window and/min
period and before-L requests at client, and crank. -/
structure Deployed {T : Protection D} {A : Supply.Delays T} {Z : Bar A} (U : Wait Z) (hG : G.Simple)
    (a : Levels G) (H P : Horizon a) : Prop where
  run : Paid (Push.Corrected.Zone.Coverage.seats hG U) a
  plates : Rack a M.X P
  sought : Present a P M.l
  keeps : Bid.Retained H P
  promise : H.Suffices M.K
  history : Doors.Budget a V.source L.W
  grow j : (a.clock.stage j).order=J.k j ∧ (a.clock.stage j).power=J.pow j ∧ (a.clock.stage j).supportExponent=J.width j

lemma deployed (hG : G.Simple) (E : Available M S L n β) (v : Increments D) {power} {T : Protection D} {B P : Supply.Delays T}
    (r : Rail M S L (β:=β) v B P power) (Y : Bar P) (U : Wait Y) :
    ∃ (a : Levels G) (H P : Horizon a), Deployed U hG a H P := by
  obtain ⟨a,H⟩ := (Push.Corrected.Zone.Coverage.seats hG U).ready hG
  have hp : Upgrade M.p L.s := Upgrade.chain S.cost L.cost
  have hKernel := H.kernel.trans hp.kernel
  have hQ : ∃ K P : Horizon a, Rack a M.X P ∧ Present a P M.l ∧
      Bid.Retained K P ∧ K.Suffices M.K := by
    have he := Next.Free.credit_from_sheet H M.γ M.b (fun i _ => (hp.direct _).trans_le (M.clip i).1)
        (fun i _ => (M.tall i).trans (E.higher i))
    obtain ⟨K,hK,HX⟩ := Next.Free.shelves a M.X M.l M.γ M.b (by rw [hKernel]; exact M.pledge) he
    obtain ⟨C,hC,hQ⟩ := M.rollback L.s hp a H.stage hKernel K hK
    exact ⟨C,K,hK,HX,hC,hQ⟩
  obtain ⟨K,P',hK,hP,HX,hS⟩ := hQ
  refine ⟨a,K,P',H,hK,hP,HX,hS,E.history D a H.lengths H.stage (fun i => ?_),fun j => ?_⟩
  · exact (r.book (a.clock.J (i+1))).trans (H.pays i)
  have H' : a.clock.stage=L.s.profile := H.stage
  rw [H']; exact L.grown _

/-- Before seeing an actual nonlinear history, precompute H with
harmonic and room. Analytic thermal/β promises still exact hypotheses
on these data (`Rates`). Rebase top before ANY nonlinear executions; can
then consume exact Oust method of Design (no INPUT asserting Oust) and
maintain ONE Directed. -/
def ceiling (P : Price D) (X : Increments D) : PostCost D :=
    ⟨P.gap,X.gamma,X.distance,X.fuel.strength,P.positive,X.positive,X.active, fun _ => Rebuild.Fuel.strength_pos ..⟩

open Input
structure Launched {T : Protection D} {A : Supply.Delays T} {Z : Bar A} (U : Wait Z) (hG : G.Simple)
    {a : Levels G} {H : Horizon a} (F : Kin H (chart G)) (K : PostCost D) (H' : Horizon a) (F' : Kin H' (chart G)) : Prop where
  native : F.Planned K
  harmonic N m : m<N → Harmonic (H.towers N m)
  receipt N m : m≤N → Ticket H M.K R.U R.A N m (F.path N m)
  credit : H'.Suffices S.O
  finalPlan : F'.Planned K
  overlays : WilsonStartup.Change.Overlay H' H
  mapped : F'.path=WilsonStartup.Change.revised F
  beta : F'.alpha=F.alpha
  fires (F₀ : Builder.Gates a) (h : F₀.Pass) (paid : Paid (Push.Corrected.Zone.Coverage.seats hG U) a) :
    ∀ N p, Oust (Builder.assign paid (chart_ok G) credit finalPlan F₀) N p



end YM.Further.PhysicalPeriodLimitF933.Timing
