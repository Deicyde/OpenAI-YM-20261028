import YM.RemainderComparison.Profile.Grant
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry

/-!
 # Further stage warrants to pay (finite demands per uptake).
 Monotone extension; applies in actual Offering/calls with this Sector.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Profile
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux
open Further.PhysicalPeriodLimitF933 Further.PhysicalPeriodLimitF933.Mural
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {D : Rolls s} {R : Targets s K} {L : Expenses R}
    {v : Return.Wages} {A : ℕ→ℝ} (P : PhysicalNext.Repeat.Register D L v A)

structure Bidder (D : Rolls s) where
  breadth (j i : ℕ):ℕ
  goal (j i : ℕ)(x : Fin (breadth j i)): Profile.Wish G (D.L j)

abbrev Receipt (h:Bidder D) := ∀ (j i: ℕ),Fin (h.breadth j i) → Wish.Terms
variable (H:Bidder D)
local notation "ι" => s.kernel

def Shipment (T: Receipt H) : Prop:= ∀ j i,4 ≤ j→ StepStages j i→ ∀ u : Fin (H.breadth j i),
    let a:= T j i u; 0<a.wick ∧ Reserve G (D.L j) a.radius ∧ Reserve G (D.L j) a.charge ∧ Reserve G (D.L j) a.purse

def Rapport (T: Receipt H) (j i: ℕ) (h : 4 ≤ j) (u:Fin (H.breadth j i)) : ℝ→Prop:=
    Wish.Receives (R j i) (P.o j i) ι (Mural.sheet s D h) (s.profile j) (s.profile i) (P.μ j i) (H.goal j i u) (T j i u)
variable {Q : Protection D}

def Committee (X : Delays Q) (T:Receipt H) : Prop:= ∀ j i,StepStages j i→ ∀ (u : Fin (H.breadth j i))(h:4 ≤ j) v,X.betaEntry j≤v → Rapport P H T j i h u v

lemma Committee.add {X Y : Delays Q} {T : Receipt H} (h : Committee P H X T) (he : DelayLe X Y) : Committee P H Y T:= fun j i hp u hv v ht=> h j i hp u hv v ((he.beta _).trans ht)
lemma sponsors (T₀: Delays Q) : ∃ T:Receipt H, Shipment H T ∧ ∃ W : Delays Q, DelayLe T₀ W∧ ∀ Y : Delays Q,DelayLe W Y→ Committee P H Y T := by
  have hm (j i : ℕ) (u : Fin (H.breadth j i)) : ∃ a: Wish.Terms, ∀ (hj : 4≤j),StepStages j i→ (0<a.wick ∧ Reserve G (D.L j) a.radius ∧ Reserve G (D.L j) a.charge ∧ Reserve G (D.L j) a.purse) ∧
      ∀ᶠ x in atTop, Wish.Receives (R j i) (P.o j i) (s.kernel) (Mural.sheet s D hj) (s.profile j) (s.profile i) (P.μ j i) (H.goal j i u) a x:= by
    let e: Wish.Terms:=⟨0,0,0,0,0⟩; by_cases hp:4≤j ∧ StepStages j i
    · obtain ⟨Q,hQ,ha,hr,hv,H⟩:= Wish.ledger (R j i) (P.o j i) (s.kernel) (Mural.sheet s D hp.1) (s.profile j) (s.profile i) (P.μ j i) (H.goal j i u) (P.consumes j i hp.2).2.1
      exact ⟨Q,fun _ _=>⟨⟨hQ,ha,hr,hv⟩,H⟩⟩
    exact ⟨e,fun h hQ => (hp ⟨h,hQ⟩).elim⟩
  choose a h using hm; have ht j i (h':StepStages j i) : ∀ᶠ x:ℝ in atTop, ∀ (u: Fin (H.breadth j i))(hj:4≤ j), Rapport P H a j i hj u x:= by
    by_cases he: 4≤j
    · apply eventually_all.mpr; intro u; exact (h j i u he h').2.mono fun x hx _=>hx
    exact Eventually.of_forall fun _ _ h=> (he h).elim
  obtain ⟨X,-,hx,hX⟩:= collect_upper T₀.betaEntry _ (fun j=>eventually_transitions j _ _ (ht j))
  exact ⟨a,fun j i he h' t=> (h _ _ t he h').1,{T₀ with betaEntry:=X},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun Y hy j i h u hj v hp=> hX j v ((hy.beta j).trans hp) i h u hj⟩
end YM.RemainderComparison.Profile
