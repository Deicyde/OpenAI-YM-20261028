import YM.UVExtension.Above.Candles
import YM.UVExtension.Dales.Rainbow
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Dales
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
open Whirl PhysicalNext.Repeat.Graces
open Above Oriel Oriel.Charted WilsonStartup Start
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    {N n:ℕ}
local notation "a!"=> A.B.a
local notation "c!"=> A.B.a.budget N
variable (hp: Allows A.B.a N) (hk:Planned.Port.AtTop A.B.kin)
    {x:ℝ} (hv:x∈band A.B.a N)
include hk hp

def headA (_R:Factor A) (N n :ℕ)(x:ℝ):= Above.temple A.B.kin N n x
lemma above_s (n:ℕ) (v:ℝ)(hv:v∈band A.B.a N): (headA R N n v).activities.Valid (A.B.a.budget N) (A.B.a.clock.allowance N) (A.B.a.clock.forcedAllowance N) := (Above.sitting A.B.kin N n hk hp hv).ingredients.gates ..
omit hk hp in
lemma betweenP (T:Levels G) (i:ℕ): T.clock.hatBeta i∈band T i:= by have he:= T.fits.delayed i; constructor <;> linarith
abbrev fieldA (N n : ℕ)(x:ℝ):= ((headA R N n x).activities.E,(headA R N n x).activities.K)

def maiden (hp: Allows A.B.a N) (n:ℕ) : Cham a! N n where
   root := fieldA R N n (A.B.a.clock.hatBeta N)
   checks := ⟨_,_,above_s R hp hk n _ (betweenP _ N)⟩
   run s b:= Above.sail A.B.kin N n s b (A.B.a.clock.hatBeta N)
include hv in
lemma maiden_t {V:Cham A.B.a N n}(H:V=maiden R hk hp n): Tabernacle.copied (A.B.a.budget N) V (fieldA R N n x):= by
    rw [H]; refine ⟨⟨_,_,above_s R hp hk n x hv⟩,fun s b=> ⟨Above.sail A.B.kin N n s b x,Above.masts ..⟩⟩

variable {V:Cham A.B.a N n}(H:V=maiden R hk hp n)
def city : Valve N n A.B.a V:= ⟨fieldA R N n x, maiden_t R hp hk hv H⟩
def singleA (b:ℝ) : Valve N n A.B.a V:= if hv:b∈band a! N then city R hp hk hv H else 0
include H
lemma high_s : headA R N n x= mount R N N n (city R hp hk hv H).val x 0:= rfl
lemma attune : Reality A.B.a N n V (city R hp hk hv H) x:=⟨hv, (tapT N n A.B.a V _).2 (above_s R hp hk n x hv)⟩
omit H
include R hv
lemma sparkA (n:ℕ): let T:=headA R N n x; Lives A.B.bake N N n T ∧ A.B.bake.Starter N n T∧ HasSlots T.p T.activities:= by
   intro F; have h:= Above.sitting A.B.kin N n hk hp hv
   rw [R.machine.ready]
   refine ⟨⟨rfl,rfl,rfl,⟨A.B.support.cap N N le_rfl,h.ingredients.gates ..⟩,Progress.DirectedRecipe.PeriodFuture.begin hv h⟩, Progress.DirectedRecipe.starter h hv _ _, h.ingredients.spare_room ..⟩
omit hv
variable {ε C:ℝ}(s:Entry A.B.a N ε)(he:0≤ ε) (ht:InsideB (A.B.a.clock.hatBeta N) C)
include s he ht H
-- ignore fake input. use same c-sheet.
def clearing (C:ℝ) (v:Flows A.B.a N n V):= place A.B.a N n V (singleA R hp hk H (art (A.B.a.clock.hatBeta N) C v.1))
lemma born :∃ F, Dales.Order (d:=V) (clearing R hp hk H C) ε F:=by
    suffices h: Oriel.Charted (river A.B.a N n V) (clearing R hp hk H C) ε by obtain ⟨F,hF,a,b,c⟩:= conquest _ (V.weather ..) h; exact ⟨F,⟨hF,a,b⟩,c⟩
    have hy(i:Arbor): C+stretchB (A.B.a.clock.hatBeta N)*i.val none∈RG.Shoot.band A.B.a N:= by
      have h: (inspire (A.B.a.clock.hatBeta N) C (lever.call i) none).re ∈RG.Shoot.band A.B.a N := (Above.fly s ht (lever.within _)).1
      rw [← show Lamppost.hoist i.val= lever.call i from rfl, Lamppost.audits] at h; exact h
    let D₁ i:= city R hp hk (hy i) H; obtain ⟨hx,hh⟩:= Above.bidT A.B.kin n hp s ht
    have hS := fundedP N a!; obtain ⟨X,hX,hA,hB⟩:=Tabernacle.heading (A.B.a.budget N) V _ _ ε D₁ hS.1 hS.2 he hx hh
    constructor; intro v h; have hk'(i): |(v i).1|≤1:= le_trans (le_max_left _ _) ((eddies ..).symm.trans_le (h i))
    apply reed v _ X hX hA hB hk'; intro w hW; let e:= Rhue (fun i=> (v i).1) w hk' hW; unfold clearing; rw [Dales.photo _ v w hk' hW]; change _=place A.B.a N n V (singleA R hp hk H (C+stretchB (A.B.a.clock.hatBeta N)* e.val none)); unfold singleA; rw [dif_pos (show _ from hy e)]
end YM.UVExtension.Dales
#print axioms YM.UVExtension.Dales.born
