import YM.UVExtension.Wren.Stoke
import YM.UVExtension.Camp.Veto
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
namespace Unum
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A) (h: Tags.Tax R.shape A.delay) {M:MapPrices}
variable {t:ι→ℕ} (F:Free.Report A.B.M M) (U:Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha)
variable (he: Tendsto t v atTop)
variable {m n : ℕ}
variable [v.NeBot][v.IsCountablyGenerated]
variable (hm:∀ n,m< t n) (hv: cashr (A:=A) v t m)(hh: cashr (A:=A) v t (m+1))
variable (hG:G.Simple)(S:Spire.Uses R hG)(m n)
variable (b : ℕ→ℝ)(x:WordsI S (m+1) n)
variable (hp:∀ n',chestR S b m n x (t n'))(hB:Arrives b)
   (hX:Arrives (fun i=> drawerE S i (m+1) n (x i)))
include hX hB hp he
lemma inputs : StableR v (fun i=> mount R (t i) (m+1) n (x (t i)).val (b (t i)) 0) :=by
   let Q n':=(x (t n')).val; obtain ⟨c,hc⟩:= hX; have hh:=(Verso.won (A.B.a.budget (m+1)) _ _ (fundedP ..|>.1) (fundedP ..|>.2) (x:=Q) (fun i=> ((S.fits (t i) n).W (m+1)|>.income _ (x (t i))|>.1)) ⟨_,hc.comp he⟩)
   let a:= (A.B.a.budget (m+1)); let F i := mount R (t i) (m+1) n (x (t i)).val (b (t i)) 0
   have hx : Transit v (fun n j (V:Config G _)=> (F n).activities.regularOccurrence (F n).p j V):= TransitM.under (G:=G) hh.1
   obtain ⟨a,hb⟩:= hB; obtain ⟨T,H,h'⟩:=hx.rain; obtain ⟨C,hV,hY⟩:=hh.2.rain
   refine ⟨⟨fun _ _=>rfl,fun _ _=>⟨rfl,rfl⟩⟩,⟨a,hb.comp he⟩,⟨C,hV,hY⟩,⟨T,H,h'⟩, fun j ε hε=>?_⟩
   filter_upwards [(hh.2.meters j).uv ε hε,(hx.meters j).uv ε hε] with v hV hz V; exact ⟨hV V,hz V⟩ -- norm dist definitional

include F U h hm hv hh
lemma spell : (∃ z, Tendsto (fun i=> Camp.compass S b m n x (t i)) v (𝓝 z))∧∃ z,Tendsto (fun i=>drawerE S (t i) m n (wood S b m n x (t i))) v (𝓝 z) :=by
    let a:= A.B.a; let K i:= (S.fits (t i) n).charts m (hm i); let Q i:=mount R (t i) (m+1) n (x (t i)).val (b (t i)) 0; let H i:= Tour.oracle R (K i) _ (hp i) 0
    obtain ⟨hs,hE,hK⟩:= Unum.perfect R h F U he hm hv hh K Q H (inputs R he m n hG S b x hp hB hX) hG
    constructor
    · unfold Camp.compass Tour.claim; simp_rw [dif_pos (hm _),dif_pos (hp _)]; exact hs
    let f i:= (wood S b m n x (t i)).val
    have hf i : f i= (K i).cores R _ (hp i):=by unfold f wood; rw [dif_pos (hm i),Tour.choiceV,dif_pos (hp i)] 
    have hp' i : (funds R K Q H i).activities.E=(f i).1 ∧ (funds R K Q H i).activities.K=(f i).2:=by rw [hf]; exact ⟨rfl,rfl⟩
    simp_rw [(fun i=> (hp' i).1)] at hE; simp_rw [(fun i=>(hp' i).2)] at hK
    exact Verso.visible (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) hE hK
omit hp hX hm hB he hv hh
open Spire
-- ALL N. discard finite prefix. shifting data is not selecting subsequence.
omit F U h in
private lemma fairtail {X: Type*} [TopologicalSpace X] {f:ℕ→X}{n}(h:Arrives (fun i=>f (i+n))): Arrives f:=by
    obtain ⟨x,hx⟩:=h; exact ⟨x,(by rw [← tendsto_add_atTop_iff_nat n]; exact hx)⟩ -- inspect
lemma commute : Camp.Sign S :=by
    constructor; intro m n b x hp hB hX; obtain ⟨K,hK⟩:= tier (A:=A) U m; obtain ⟨J,hJ⟩:= tier (A:=A) U (m+1); obtain ⟨B,hp⟩:=eventually_atTop.mp hp
    let j:=K+J+B+m+1; let t (i:ℕ):= i+j; have hm(i): m< t i:= by unfold t j; omega
    have hV:Tendsto t atTop atTop:= tendsto_atTop_mono (f:=id) (fun i=> by unfold t; simp) tendsto_id
    obtain ⟨he,hF⟩:= spell R h F U hV m n hm (hK _ _ t hV (fun i=>(hm i).le) (by unfold t j; omega)) (hJ _ _ t hV hm (by unfold t j; omega)) hG S b x (fun k=>hp (t k) (by unfold t j; omega)) hB hX
    exact ⟨fairtail he, fairtail hF⟩
end Unum
end YM.UVExtension.Roads
#print axioms YM.UVExtension.Roads.Unum.commute
