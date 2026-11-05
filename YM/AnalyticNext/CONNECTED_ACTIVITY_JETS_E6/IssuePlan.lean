import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fire
import YM.Push.PRICE_COMPILER.Basic



/-!
# Before Teller schedule: buying these estimates simultaneously

Only evaluation data. Paid direction may need restrictions from MANY
other costs e.g. order Θ after using smooth estimates. Quantify stages
WITH targets, give true Cash for every period/R Move test on a common
post-L and W. No promise that every accepted schedule is afforded or
that B.M is freely chosen on it. Time schedule ensures α→matrix at
that literal Energy query. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees    PriceCompiler
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f n : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {a α W μ C : ℝ} {R : Rep G f} {L : Side}
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W}

namespace Target

lemma baseline (G : Gauge) (W : ℝ) : Nonempty (Order G W) :=
    ⟨⟨1,1,1,0,1,0,1,1,1, ⟨zero_lt_one,zero_lt_one, le_rfl,le_rfl⟩,zero_lt_one,by norm_num,zero_lt_one⟩⟩

/-- Includes renewal for excursions. -/
structure Expense (Q : Target G P) where
  degrees : ℕ
  earn : ℝ       -- wanted support exponent after restores
  one : ℝ
  two : ℝ
  wanting : ℝ    -- desired analytic power for urgent quantum
  price : 0 ≤ earn
  first : 0 < one
  second : 0 < two
  worth : earn+two+one ≤ Q.exp
  reach : Q.rate < wanting
  arrives : wanting < 0

def Ledgered (X : Expense Q) (L : Side) (W μ c : ℝ) (o : Order G W) (x : ℝ) :=
    Q.mergeScale L μ x X.degrees ≤ Pressure.betaF G x L ^ X.wanting ∧
    ∀ (c' f : Side) (S : StepData c' f) (T : Tube G S), Works P L x S T →
      (PointCharge T x W μ ∧ Charged T x W μ) ∧
      (Stamp T → ∀ R : Rep G f, Intake P T x R → ∃ H : Cash W x μ L Q o c T R, Cash.Renewed X.degrees X.earn X.one X.two H)

theorem quotesTogether (Q : Target G P) (X : Expense Q) : ∃ n : ℕ, ∀ L : Side, n≤L.val →
    ∀ᶠ W in atTop, 0<W ∧ ∃ (μ c : ℝ) (o : Order G W), 0<μ ∧ 0≤c ∧ ∀ᶠ x : ℝ in atTop, Ledgered X L W μ c o x := by
  obtain ⟨n,hn⟩:=Q.issue; refine ⟨n,fun L hL=> (hn L hL).mono fun w hw=> ⟨hw.1,?_⟩⟩
  obtain ⟨hw,μ,hμ,h⟩:=hw
  by_cases he : ∃ D : Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap
  · refine ⟨μ,0,Classical.choice (baseline G w),hμ,le_rfl,?_⟩
    filter_upwards [Q.tempo L hμ X.degrees X.wanting X.reach] with x hx
    exact ⟨(le_abs_self _).trans hx,fun _ _ S T hp=> (he ⟨S.patch,hp.funds.kernel,hp.length_eq,hp.funds.atStep⟩).elim⟩
  obtain ⟨D,he,hD,hP⟩:= he
  obtain ⟨o,C,hC,hr⟩:= h D he
  refine ⟨μ,C,o,hμ,hC,?_⟩
  filter_upwards [hr,Q.tempo L hμ X.degrees X.wanting X.reach,Cash.anew Q L o C hμ X.degrees X.price X.first X.second X.worth] with x h H hf
  refine ⟨(le_abs_self _).trans H,fun c f S T hw=> ?_⟩
  obtain ⟨ht,hv⟩:= h c f S T (hw.patch hD hP) hw
  refine ⟨⟨ht.grant,ht.grant.charged hw.funds⟩,fun hp R hR=>?_⟩
  obtain ⟨h'⟩:= circulates (hv R hR hp); exact ⟨h',hf c f S T R h'⟩
end Target

open RG.Supply Pressure.Testing
namespace Planning
variable (C : Sheet G) (M : MapPrices) (Q : ∀ j i,Target G (query C M j i))
variable (p : ∀ j i,Target.Expense (Q j i)) (D : Supply.Rolls C)

def Need (x : ℕ→ℕ) : Prop := ∀ j i, StepStages j i→∀ L : Side,x j ≤ L.val→
    ∀ᶠ W in atTop,0<W ∧ ∃ (μ c:ℝ) (o:Target.Order G W),0<μ ∧ 0≤c ∧ ∀ᶠ z in atTop, Target.Ledgered (p j i) L W μ c o z

lemma exists_floors : ∃ x : ℕ→ℕ, Monotone x ∧ C.floorL≤x ∧ Need C M Q p x := by
  choose u hu using fun j i=> Target.quotesTogether (Q j i) (p j i)
  let g (j : ℕ) := max (C.floorL j) (fromMax u j)
  exact ⟨prefixHi g,prefixHi_mono g,fun i=> (le_max_left ..).trans (le_prefixHi g le_rfl),
    fun j i h L he=> hu j i L (((le_fromMax u h).trans (le_max_right ..)).trans
      ((le_prefixHi g le_rfl).trans he))⟩

variable (w : ℕ→ℕ→ℝ)

structure Purchase (P : ℕ→ℝ) where
  μ : ℕ→ℕ→ℝ
  c : ℕ→ℕ→ℝ
  o : ∀ i j,Target.Order G (w i j)
  consumes i j (he : StepStages i j) : 0<w i j ∧ 0<μ i j ∧ 0≤c i j ∧
    ∀ x : ℝ, P i ≤ x → Target.Ledgered (p i j) (D.L i) (w i j) (μ i j) (c i j) (o i j) x

/-- C.target depends even on both stage indices. p Θ chart data before
roller; rates can be changed by max operations. -/
theorem waits {x : ℕ→ℕ} (h : Need C M Q p x) (he : ∀ j,x j ≤ (D.L j).val) :
    ∃ k : ℕ→ℝ, Monotone k ∧ ∀ w : ℕ→ℕ→ℝ, (∀ j i, StepStages j i → k j ≤ w j i) →
      ∃ X : ℕ→ ℝ, Monotone X ∧ (∀ i, 0<X i) ∧ Nonempty (Purchase C M Q p D w X) := by
  obtain ⟨k,hk,-,hp⟩:= collect_upper (fun _=> (1:ℝ)) _ fun j => eventually_transitions j atTop _ (fun i hi=> h j i hi (D.L j) (he j))
  refine ⟨k,hk,fun w hw=>?_⟩
  have hh (j i : ℕ) : ∃ (μ c:ℝ) (o : Target.Order G (w j i)), StepStages j i → 0<w j i ∧ 0<μ ∧ 0≤c ∧ ∀ᶠ x in atTop,
      Target.Ledgered (p j i) (D.L j) (w j i) μ c o x := by
    by_cases ht : StepStages j i
    · obtain ⟨hw,μ,c,o,hv,hc,hh⟩:= hp j _ (hw _ _ ht) i ht
      exact ⟨μ,c,o,fun _=> ⟨hw,hv,hc,hh⟩⟩
    exact ⟨0,0,Classical.choice (Target.baseline G _),fun hf => (ht hf).elim⟩
  choose μ c o hh using hh
  obtain ⟨g,hg,hg',hp⟩:= collect_upper (fun _=> (1:ℝ)) _ fun j=> eventually_transitions j atTop _ (fun i hi=> (hh j i hi).2.2.2)
  exact ⟨g,hg,fun j=> zero_lt_one.trans_le (hg' j),⟨⟨μ,c,o,fun i j he=> ⟨(hh i j he).1,(hh i j he).2.1,
    (hh i j he).2.2.1,fun x hg=>hp i x hg j he⟩⟩⟩⟩
end Planning
end YM.ConnectedActivityE6
