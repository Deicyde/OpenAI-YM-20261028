import YM.FullVolume.E6.Gest
import YM.FullVolume.Sym.Avenues
import YM.FullVolume.C.Songbook

/-! Entry prices after both transition buys. Require STEP and comparisons LBelt.
    no assertions yet shrinking Hℓ widths -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Jams
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Marlin Empire Time
open FullVolume.Ray
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {Q: Targets s K} {Z: Expenses Q}
abbrev Zoo {W μ C x:ℝ} {L:Side}{P:Teller G}{Q:Target G P}(o:Target.Order G W) (k:Bank) (j:ℕ):=∀ (c f:Side) (S:StepData c f) (T:Tube G S), Works P L x S T → Stamp T→ ∀ (V:Rep G f) (H: Cash W x μ L Q o C T V), Nonempty (Station k Chi.canonical H j)
def zoo_post {P:Teller G}(Q:Target G P) (L:Side) (i:ℕ):=∀ (W μ C:ℝ),0<W→0<μ→∀ (o:Target.Order G W),∀ᶠ x in atTop, ∃ k,Zoo («Q»:=Q) (L:=L) (μ:=μ) (C:=C) (x:=x) o k i
lemma safari {P : Teller G}(Q:Target G P)(hp:0<Q.exp):∃ n:ℕ,∀ L: Side,n≤L.val → ∀ i, zoo_post Q L i:= by
  obtain ⟨n,hL⟩:= patrol P Q; refine ⟨n,fun L hl i W μ C hw hm o=>?_⟩
  by_cases he:∃ D:Patch,D.Branches P.bind G ∧ D.L=L ∧ D.J=P.j
  swap; · filter_upwards with x; exact ⟨⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩,fun c f S T h=> (he ⟨S.patch,h.funds.kernel,h.length_eq,h.funds.atStep⟩).elim⟩
  obtain ⟨D,hD,h,d⟩:= he
  filter_upwards [hL L hl D hD i Chi.canonical W hw μ hm o hp C] with x hh; obtain ⟨k,H⟩:=hh; exact ⟨k,fun c f S T hS ht=> H c f S T (hS.patch h d) ht⟩
variable {D:Rolls s} {Θ:Protection D} {w:Return.Wages} {E:ℕ→ℝ}(R : Register D Z w E)
-- ledger at actual paid for all stamps on works
abbrev Wild (V:Delays Θ): Prop:= ∀ j x,V.betaEntry j ≤ x → ∀ i,StepStages j i → ∃ k,Zoo (Q:=Q j i) (L:=D.L j) (μ:=R.μ j i) (C:=R.c j i) (x:=x) (R.o j i) k (s.profile i).order
lemma supplies (V:Delays Θ)(h:∀ i j,StepStages j i→zoo_post (Q j i) (D.L j) (s.profile i).order):∃ U:Delays Θ,DelayLe V U∧∀ W:Delays Θ, DelayLe U W→ Wild R W:= by
  obtain ⟨x,-,hx,hS⟩:=collect_upper V.betaEntry _ fun j=> eventually_transitions j _ _ fun i h'=> h i j h' (w j i) (R.μ j i) _ (R.consumes j i h').1 (R.consumes j i h').2.1 (R.o j i); exact ⟨{V with betaEntry:=x},⟨hx,le_rfl,le_rfl,le_rfl⟩,fun W H j y hy=> hS j y ((H.beta j).trans hy)⟩
lemma herds (Q:Targets s K) (hp:∀ j i, (s.profile i).supportExponent+3<(Q j i).exp): ∃ x:ℕ→ℕ, ∀ j i,StepStages j i→∀ L:Side,x j≤ L.val→∀ w,zoo_post (Q j i) L w:=by
  choose u hx using fun j i=> safari (Q j i) (lt_trans (add_pos ((s.profile i).price_pos) (by norm_num)) (hp j i))
  exact ⟨fromMax u,fun j i h L he=> hx j i L ((le_fromMax u h).trans he)⟩
end YM.PhysicalNext.Repeat.Jams
