import YM.UVExtension.Wren.Roads
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
variable (V : ∀ i:ι, Zeal R.target R.shape A (t i) m) (x:ι→ lands A m) (P:ι→ℕ)(X':RG.Rep G (A.B.a.S.side (m+1) n))
    (hX:∃ k,Tendsto (fun n=>(x n).val) v (𝓝 k))(hp:Tendsto P v atTop)
include X' hX hp hm U h F hv hh he
lemma children (a:Stars) : Aside.Stars v (A.B.a.budget m) (fun n => (V n).offers (P n) (x n) a):=by
    obtain ⟨n,h⟩:= (show ∀ᶠ i in v,True from by simp).exists -- he preserve
    let H i:=(V i).tiers a (x i)
    let t':=Rain.panes R.target A m a; let Q i:= Racks R.target A (t i) m a (x i).val
    obtain ⟨T⟩:= fares R ‹Tags.Tax R.shape A.delay› F he hm hv hh t' Q H
    have hv : StableR v Q:=by
       have he i j x : (Q i).activities.K j x=0:=rfl
       have hh i j x:(Q i).activities.regularOccurrence (Q i).p j x=0:=by change masked _ _ 0 x=0; simp [masked]
       refine ⟨⟨fun i j=> rfl,fun i j=>⟨rfl,rfl⟩⟩,hX,⟨_,Swift.nil (fun (_:ℕ)=>0) (u:=0) (by simp [SumBudget]),?_⟩,⟨_,Swift.nil (fun (_:ℕ)=>0) (u:=0) (by simp [SumBudget]),?_⟩,fun j ε ht=> ?_⟩
       · filter_upwards with i j X; rw [he,abs_zero]
       · filter_upwards with i j X; rw [hh,abs_zero]
       filter_upwards with i X; rw [he,he,hh,hh,dist_self]; exact ⟨ht.le,ht.le⟩
    exact T.skyline hv n _ _ _ hp (pacing m U _ he) rfl le_rfl (Guild.hp_width R (hm n) X').1
omit X' hX hp
variable {ε:ℝ}
variable (g:∀ i,Tour R (t i) m n ε)(H:∀ i,RG.Rep G (A.B.a.S.side (m+1) n))(J:∀ i:ι, Item R (N:=t i) (P:= mount R (t i) (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0) (H i)) (hT: StableR v H)

def songs (i):= (J i).song R (g i).atTopH (g i).W (g i).k
def placeR (i:ι):= Guild.Market R (g i).atTopH
def funds (i):= Item.issue R (g i).atTopH (g i).W (g i).k (J i)
variable (hG:G.Simple)
include hT hG
set_option maxHeartbeats 300000 in
lemma perfect : (∃ t', Tendsto (fun i=> Item.coupon R (g i).atTopH (g i).W (g i).k (J i)) v (𝓝 t'))∧
    Notes v (A.B.a.budget m) (drawer G _).reg (fun i=>(funds R g H J i).activities.E) ∧ Transit v (fun i j V=> (funds R g H J i).activities.K j V):=by
    obtain ⟨p',hh'⟩:= (show ∀ᶠ i in v,True from by simp).exists
    let Q i:= (J i).atH; let k:= A.B.a.S.oneStep m n; obtain ⟨U'⟩:= Unum.fares R h F he hm hv hh k.exact_size H Q
    let t':= fun i=> (g i).k; have hx:Tendsto t' v atTop:= tendsto_atTop_mono (fun i=> (g i).enough) he
    let c:= (A.B.a.budget m); let b i:lands A m:=⟨(H i).beta,(J i).aisle⟩; let X i:=(g i).W.offers (t' i) (b i)
    let z:=(Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))); let Y:= placeR R g p'
    let Fk:= A.B.a.S.side m n; have hz : ∀ i, Beam.marquee ((J i).atH) c=Beam.marquee ((g i).atTopH) c:=fun i=> (samePoster (H:=(g i).atTopH) (H':=Q i) c (J i).related).symm
    have hu i: placeR R g i=Y:=by
      change pluck _ (Marlin.lodge (Beam.marquee (g i).atTopH c) _ _)=pluck _ (Marlin.lodge (Beam.marquee (g p').atTopH c) _ _)
      rw [←hz,← hz, show Beam.marquee ((J i).atH) c= _ from U'.versed hT p' c i]; rfl
    have ht:=(Guild.hp_width R (hm p') (H p'))
    have hX i:Aside.Stars v c (fun n=> X n i):= Unum.children R h F U he hm hv hh (fun n=> (g n).W) b t' (H p') hT.beta hx i
    let K i:= (J i).song R (g i).atTopH (g i).W (g i).k; let C:=Rain.screens R.target A m; let d i:=A.B.kin.alpha (t i) m; have hk i : K i= Wren.Choir.freshW (H:=Q) c d t' C (w':=z) X i := sameArts (A.B.a.budget m) _ _ (J i).related (J i|>.links R _) _ rfl rfl _ _ (show Cousin (H i) (H i) from ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩)
    have hp₀ := pacing (A:=A) m U _ he
    have he₁ : Notes v c Y.reg (fun n=>(K n).logRead)∧ Transit v (fun i=>(K i).hardRead):=by
        simp_rw [hk]; have hg:= U'.barline hT p' c d t' hx hp₀ rfl le_rfl ht.1 C (w':=z) (by unfold z Trio.base; omega) X hX
        rw [show Y=bookA (Beam.marquee (Q p') c) z c from (congr_arg (fun p=>bookA p z c) (hz p').symm)]; exact hg
    constructor
    · let r i:=Averaging.delta (Y.read (K i)); rw [show (fun i=>_)=r from ?_]; exact Crumble.pursuit he₁.1 hG -- need hG
      funext i; unfold Item.coupon r; rw [← hu]; rfl
    obtain ⟨W,hq⟩:=hv; let f i:=(J i).issue R (g i).atTopH (g i).W (g i).k; let w:ι→ℝ:= fun i=>(f i).beta; let g' i:=(f i).v
    have hR i:f i=Crumble.deed (Z:=(A.B.a.params m).clip) (A:=Y) (K:=K) (Q:=fun i=> A.B.kin.path (t i) m) (α:=d) c w g' i:=by
        let Z:=A.B.kin.path (t i) m; let c':=(A.B.a.params m).clip; exact congr_arg (fun X=> finish Z c' c (shelves X Z c) (branch X Z c' c (K i) (d i)) (w i) (g' i)) (hu i)
    change Notes v _ _ (fun i=>(f i).activities.E) ∧ Transit v (fun i j V=> (f i).activities.K j V); simp_rw [hR]
    obtain ⟨u,h⟩:= hp₀; exact Crumble.bought c hq ht.1 ht.2 h he₁.1 he₁.2 hG w g' -- hG
end Unum
end YM.UVExtension.Roads
