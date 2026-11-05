import YM.UVExtension.Wren.Singer
import YM.UVExtension.Spire.Spark
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Roads
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open PhysicalNext PhysicalNext.Repeat
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof Roost
open Progress.DirectedRecipe Time Rain
open Wick Lamppost YM.UVExtension.Concert
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Guild Tabernacle
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
open Reward Wren Steady Span
variable {G:Gauge}{ι:Type} {v:Filter ι} {T:Levels G}
namespace Tags
-- request buys strictly pre-L then delays.
variable (s:Supply.Sheet G) (K:MapPrices)(X: Targets s K)
def Rents (f:ℕ→ℕ):Prop := ∀ i j:ℕ, StepStages i j→∀ (L:Side), f i ≤ L.val→ ∀ (o μ:ℝ)(U:Target.Order G o),0<o → 0<μ → 0<(X i j).exp → ∀ᶠ x in atTop,Hikes.Ledger (X i j) L o μ U x (s.profile j).order Chi.canonical
lemma salts :∃ f:ℕ→ℕ,Rents s K X f:=by
    choose f hf using fun i j=>Hikes.purchases (X i j); exact ⟨fromMax f,fun i j hi L hL o μ U hv hm=>hf _ _ _ ((le_fromMax f hi).trans hL) _ _ _ _ hv hm _⟩
variable {s K X}{D:Rolls s}{Θ:Protection D}{P: Expenses X}{u:Return.Wages}{l: ℕ→ℝ}
variable (R:PhysicalNext.Repeat.Register D P u l)
def Tax (Y:Delays Θ): Prop:=∀ j i, StepStages j i → ∀ x,Y.betaEntry j≤x → Hikes.Ledger (X j i) (D.L j) (u j i) (R.μ j i) (R.o j i) x (s.profile i).order Chi.canonical
lemma fines {f:ℕ→ℕ}(hf:Rents s K X f) (hL:∀ j,f j≤ (D.L j).val)(V: Delays Θ):∃ W:Delays Θ,DelayLe V W∧∀ Y:Delays Θ,DelayLe W Y→ Tax R Y:=by
    let g j (i:ℕ)(x:ℝ):= Hikes.Ledger (X j i) (D.L j) (u j i) (R.μ j i) (R.o j i) x (s.profile i).order Chi.canonical
    have hk j i (h:StepStages j i): ∀ᶠ x in atTop,g j i x:=by
       obtain ⟨a,b,c,d⟩:= R.consumes j i h; exact hf _ _ h _ (hL _) _ _ _ a b (by linarith [(P j i).worth,(P j i).price,(P j i).first,(P j i).second])
    obtain ⟨x,-,hv,hx⟩:= collect_upper V.betaEntry _ (fun j=>eventually_transitions j _ (g j) (hk j))
    exact ⟨{V with betaEntry:=x},⟨hv,le_rfl,le_rfl,le_rfl⟩,fun Y hy j i hi y h=> hx j y ((hy.beta _).trans h) i hi⟩
end Tags
namespace Unum
-- each purchase real auxiliaries under ANY concerted plan over given histories. Don't fix pendant mixed signs.
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) (h: Tags.Tax R.shape A.delay) (m:ℕ) {M:MapPrices}
local notation "T0"=> A.B.a

abbrev cashr (v: Filter ι) (t:ι→ℕ)(m:ℕ): Prop:=∃ d, Revenues v ((A.B.a.params m)).width (fun n=> A.B.kin.path (t n) m) d -- macros
variable (F:Free.Report A.B.M M) (U:Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha)
variable (t:ι→ ℕ)(he: Tendsto t v atTop)
include U
lemma tier (m:ℕ): ∃ K:ℕ, ∀ (ι: Type) (v:Filter ι)(t:ι→ℕ), Tendsto t v atTop → (∀ i,m≤t i)→(∀ i,K≤t i) →cashr (A:=A) v t m:=by
   obtain ⟨q,r,hp,h⟩:=U.fields m; let x:=(A.B.a.params m).width; obtain ⟨hv,hr⟩:=h _ hp
   obtain ⟨k,hk⟩:= eventually_atTop.mp hv; refine ⟨k,fun ι v t he hs hx=>?_⟩; exact ⟨_,⟨(A.B.a.params m).width_pos,fun i=> (hk _ (hx i)).1,fun i=> (hk _ (hx i)).2,fun i=> ⟨_,_,_, A.B.support.cap _ _ (hs i)⟩,fun ε hp=> he.eventually (hr ε hp)⟩⟩
include he
lemma pacing : ∃ a:ℝ,Tendsto (fun n=> A.B.kin.alpha (t n) m) v (𝓝 a):=by obtain ⟨y,h⟩:= U.prices m; exact ⟨y,h.comp he⟩ -- include he
omit U
variable {m t}
variable (hp:∀ n,m < t n) (hv: cashr (A:=A) v t m) (hh: cashr (A:=A) v t (m+1))
include he hv hh F
lemma pensions {c f:Side}(H:f.val=c.val*(A.B.a.S.block m).val): Concerted v (fun n=> Pane.orchestra A (t n) H) :=by
   obtain ⟨B,-,-,hf,hn,hZ⟩:= F.columns m; obtain ⟨T,hT⟩:= hh; obtain ⟨Q,hQ⟩:=hv
   exact ⟨⟨_,_,hT⟩,⟨_,_,hQ⟩,⟨_,fun i=>rfl⟩,⟨_,fun i=>rfl⟩,fun i j k=> ⟨_,(tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf.entries i) j) k).comp he⟩,fun i j k=> ⟨_,(tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hn.entries i) j) k).comp he⟩,fun i j k=> ⟨_,(tendsto_pi_nhds.mp (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hZ.entries i) j) k).comp he⟩⟩
variable [v.NeBot]
include hp h
lemma fares {c f :Side} (H: f.val=c.val*(A.B.a.S.block m).val)(Y:ι→ RG.Rep G f)(X:∀ n, Chartlet R.shape A (t n) m H (Y n)): Nonempty (Wren.Choir v (fun n=> Pane.orchestra A (t n) H) X ((A.B.a.budget m).order) Chi.canonical):=by
    have he':=(pensions F he hv hh H)
    have hS:∀ k, SliceRows.Stamp (Pane.orchestra A (t k) H):=fun i=> Pane.ovation A (t i) H (hp i) R.pledging.conducts.full
    have hV := h _ _ (step_paid A.B.a m) _ (A.B.valid.pays m)
    rw [show (A.B.a.budget m).order=_ from Rain.jersey (A:=A) (m:=m)|>.1]; exact hV.capitol ι v (fun n=> Pane.orchestra A (t n) H) Y _ X he' hS
end Unum
end YM.UVExtension.Roads
