import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.UVExtension.Guild.Run
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


open PhysicalNext.Repeat.Mallow UVNext.CouplingReset
variable (hG:G.Simple) (T:Crest R ε) {P:(RG.Rep G (A.B.a.S.side (m+1) n))} (H:Guide A.B R.shape N m n P)(k:ℕ)(W: Zeal R.target R.shape A N m)(hw: Wheeled R H W (ε:=ε) k)

structure Voyage (l t:ℝ) (Q:In A.B.a m n) (ρ:∀ i:(Set.Icc l t), Item R (P:=P) (N:=N) (Q i)) where
    body : Spring R N m n l t Q
    w : body.W=W
    count : body.ordinal=k
    X : body.X'=Guild.Market R H
    V : ∀ i:(Set.Icc l t), body.V' i= Item.song R H W k (ρ i)
    pay : ∀ i:(Set.Icc l t), body.result i=Item.issue R H W k (ρ i)

include T hw hm hG H
variable {l t:ℝ}(ht : l≤ t) (Q:In A.B.a m n) (Y:∀ i:Set.Icc l t, Item R (P:=P) (N:=N) (Q i)) (h: Curve (A.B.a.budget (m+1)) Q (Set.Icc l t))(he: ∀ i∈Set.Icc l t,Lives A.B.bake N (m+1) n (Q i)∧ (Q i).beta∈ band A.B.a (m+1))
include ht h he
lemma voyaging : Nonempty (Voyage R H k W l t Q Y):=by
  let A0:= (A.B.a.budget m); let E:= R.pledging; obtain ⟨J⟩:= Roof.arches E.conducts hm he h (θ:=Set.Icc l t) (y:=l) (Set.left_mem_Icc.mpr ht); let a₀:=(A.B.a.clock.hatBeta m)
  let V':= J.sister; let i₀:Set.Icc l t:=⟨l,Set.left_mem_Icc.mpr ht⟩; let H':= Y i₀; let r':= Market R H; let M:= hw
  have hbase: KinBase P (Q l):= H'.related
  let J':= Roof.Embrasure.base J
  have hh: Beam.marquee H A0=J.doors:= Concert.samePoster (H:=H) (H':=J') A0 hbase
  have hz (x:ℝ)(hx:x ∈ Set.Icc l t): Meadow.Budget A0 J.doors.reg (uptick J k x).logRead (lampFee (A:=A) (m:=m))∧ ∀ i:Site (A.B.a.S.side m n), (A.B.a.budget m).supBounds i (neighbors (Trio.base (Rain.lint R.target A m) (radiusB (A.B.a.clock.hatBeta m))) i) (beacons J he W k x i) (Rain.gleam (A:=A) (C:=R.target) (m:=m)) := by
    let i:Set.Icc l t:= ⟨x,hx⟩; let V:= Y i; let c:= J.latch x; have hc:c=i:= J.click x hx; have hL := T.limited; have ht : 0 ≤ forecastE A.B.a m:= mul_nonneg (credit_pos ..|>.le) (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    refine ⟨?_,hw.year (Rain.noteX J he x)⟩
    have hp: Tips R H k V.atH (V.links R H) = uptick J k x:=by unfold uptick; rw [show J.latch x= i from hc]; exact Concert.sameBook k (A.B.kin.alpha N m) hbase _ _ rfl (J.agrees _) ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩
    obtain ⟨f,hf,hV⟩:= hw.helm _ V.atH (V.links R H) V.related rfl V.aisle V.price
    rw [←hp,← hh]; refine ⟨_,fun t=> budget_loosen (hf t) ?_,hV⟩; unfold shoal lampFee; linarith only [mul_le_mul_of_nonneg_right hL ht]
  let S' : Spring R N m n l t Q:= ⟨h,he,J,W,k,Classical.choice (Tree.select _ (A.B.a.clock.op m n).patch.odd_side),hz⟩
  have hX : S'.X'=Market R H:= by unfold Spring.X' opening Market Concert.bookA S'; dsimp only; rw [show Beam.marquee _ _= J.doors from hh]
  have hy (x:Set.Icc l t):S'.V' x= Item.song R H W k (Y x):=by
    let v:= Y x
    change Rain.paint J he W k x=_; unfold Rain.paint Rain.graft lights uptick Rain.beacons; dsimp only; rw [show noteX J he x.val= ⟨_, v.aisle⟩ from ?_,J.click _ x.2]; swap
    · refine Subtype.ext ?_; change (Q (J.latch x)).beta=(Q _).beta; rw [show J.latch x=x from J.click _ x.2]
    apply (Concert.sameArts A0 k (A.B.kin.alpha N m) hbase (v.links R H) (V' x) rfl (J.agrees _) (Rain.screens R.target A m) (W.offers k ⟨_,v.aisle⟩) (show Cousin _ _ from ⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl⟩)).symm
  refine ⟨⟨S',rfl,rfl,hX,hy,fun i=>?_⟩⟩
  have hV : Collection.vac (S'.V' i) (S'.τ i)= flatRate A.B.a m n (Q i):= by rw [← show (S'.result i).v=_ from (S'.moves hG hm|>.2 i i.2).2.2.2]; rfl
  rw [S'.owns hG hm i.2]; rw [hV,hX,hy]; rfl
end YM.UVExtension.Guild
#print axioms YM.UVExtension.Guild.voyaging
#print axioms YM.UVExtension.Guild.Item.perfect
#print axioms YM.UVExtension.Guild.shaft
