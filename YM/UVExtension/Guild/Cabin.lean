import YM.UVExtension.Guild.Chair
import YM.UVExtension.Concert.Pure
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Guild
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

variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
   {N m n : ℕ} (hm:m<N) {ε:ℝ}


variable {P:Rep G (A.B.a.S.side (m+1) n)}(H:Guide A.B R.shape N m n P) (hr:P.p=A.B.a.budget (m+1)) (ht: WilsonStartup.Decent (A.B.a.params m).clip (A.B.a.budget m))
private theorem vacCurve {G:Gauge}{f:Side}(P:Rep G f)(q:BudgetPoint)(s:Set ℝ): Curve q (Wick.flight P) s:= ⟨continuousOn_id,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,fun ε h x hx=> by
  filter_upwards with i
  change deviation q P.activities P.activities ε
  exact ⟨0,0,fun _=> ⟨le_rfl, by simp⟩,fun _=> by simp,by simp [SumBudget,BudgetPoint.mass,h.le],by simp [SumBudget,BudgetPoint.mass,h.le]⟩⟩
include hm hr ht R H
lemma retire (k:ℝ) (hk:0<k): ∀ᶠ d:ℕ in atTop, ∀ (Y:Rep G (A.B.a.S.side (m+1) n)) (H': Guide A.B R.shape N m n Y)(X':Match.Alliance H H' 1 0), KinBase P Y → Y.beta ∈ band A.B.a (m+1) → X'.units=Equiv.refl _ →
    Meadow.Budget (A.B.a.budget m) (Beam.marquee H (A.B.a.budget m)).reg (fun i=> if Meadow.debris H d i then (Song.plusone H X' Chi.canonical (A.B.kin.alpha N m)).logRead i else 0) k:=by
  let Z:=A.B.a; let s:= band Z (m+1); let w:= PriceCompiler.step_paid Z m; let t:= R.pledging.conducts; let Q:=ships A.B N m n; let Y:=Wick.flight P; let p:= Z.budget m
  have he b (hb:b∈s): ∃ U : Guide A.B R.shape N m n (Y b), Opera.Price A.B R.shape N m n (Y b) U:=by
    obtain ⟨h₀,h₁,hV,hL⟩:= Planning.testing A.B R.shape t.income.grow.1 N m n hm
    refine ((hL.2 _ _ _ _ hV).2 (Opera.protocol A.B hm t.full) _ (Wick.retreat H.laws.intake _ ?_)); rw [hV.length_eq,← PriceCompiler.beta_eq A.B.valid]; exact hb
  choose U hU using fun i:s=> he i.val i.property; let M':=A.B.a.S.oneStep m n
  let v k:= Match.staple (H:=H) (J:=U k) rfl rfl rfl
  let o k:= Song.plusone H (v k) Chi.canonical (A.B.kin.alpha N m)
  let s₀:s:= Boulevard.phase A m; let f:ℝ→ Collection.Source G (Z.S.side m n):=Function.extend (Subtype.val (p:=fun i=>i∈s)) o (fun x=>o s₀); have he' (i:s): f i=o i := Subtype.val_injective.extend_apply o _ i
  have hn : p.order ≤ (X.p.profile (Z.clock.J m)).order:= (Rain.jersey (A:=A) (m:=m)).1.le
  have hx := Boulevard.suns R.shape A R.inn.chip hm M'.exact_size H
  obtain ⟨u,hV⟩:= R.inn.year _ _ (A.B.valid.pays m) _ w; let W i:= (hV _ _ _ Q H.laws.data.funds (Opera.protocol _ hm t.full) _ _ (U i)).some
  have h' : Compared (Beam.marquee H p) p f s:= Yearling.compared (R:=Y) p rfl hn (show Q.down.Bounds Q.low _ _ _ from A.B.support.cap _ _ hm.le) ht (hx.1.trans (show _/4 ≤ (A.B.a.params m).width/2 from by have he:=(A.B.a.params m).width_pos; linarith)) U hU W H v (A.B.kin.alpha N m) (fun _=>rfl) (Beam.dashboard H) (Beam.see H) f he' (A.B.a.budget (m+1)) (fun _ _=>hr) (vacCurve ..) (fun _ _=>⟨rfl,rfl⟩)
  have hf i:= (Boulevard.lays R.shape A M'.exact_size (v i) R.inn.chip hm R.pledging.jewels t.full (R.pledging.agenda _ _ w|>.1) ht (hU i) (Classical.choice (Tree.select _ (Pane.panel A m M'.exact_size).patch.odd_side))).1
  have hg (x:ℝ) (hx:x∈s):∃ w T, Collection.Local (posting p H) p (f x) w T:= by rw [show f x=_ from he' ⟨x,hx⟩]; exact ⟨_,_,hf _⟩
  filter_upwards [Meadow.cashier (fun i=> (Beam.rewrite_rule H p i).symm) p (Meadow.debris H) isCompact_Icc (Meadow.dissolved H) h' hg k hk] with d hd Y H' X' ha hy hY
  have he:=hd _ hy; rw [show f Y.beta=_ from he' ⟨_,hy⟩] at he
  let Z : KinBase (Wick.flight P Y.beta) Y:= ⟨ha.reg,ha.forced,ha.point,ha.path,ha.clip⟩
  let V i:= if Meadow.debris H d i then (Song.plusone H X' Chi.canonical (A.B.kin.alpha N m)).logRead i else 0
  have hh : V=(fun i=> if Meadow.debris H d i then (o ⟨_,hy⟩).logRead i else 0):= by
    funext i; unfold V; split; next hx=> exact (ages H d (A.B.kin.alpha N m) (v ⟨_,hy⟩) X' rfl hY Z rfl i hx).symm
    rfl
  change Meadow.Budget p (Beam.marquee H p).reg V k; rw [hh]; exact he
end YM.UVExtension.Guild
