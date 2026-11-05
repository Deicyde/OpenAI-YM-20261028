import YM.UVExtension.Wet.Bar
import YM.UVExtension.Wet.Comet
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wet
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
open Reward Wren Steady Span Roads.Unum
variable {G:Gauge}{ι:Type} {v:Filter ι} {T:Levels G}
variable {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Roost.Factor A) (h: Roads.Tags.Tax R.shape A.delay) {M:MapPrices}
variable {t:ι→ℕ} (F: UVExtension.Free.Report A.B.M M) (U:Reward.Ends A.B.a A.B.kin.path A.B.kin.alpha)
variable (he: Tendsto t v atTop)
variable {m n : ℕ}
variable [v.NeBot][v.IsCountablyGenerated]
variable (hm:∀ n,m< t n) (hv: cashr (A:=A) v t m)(hh: cashr (A:=A) v t (m+1))
-- hub only at exact bait (U.price constant input. H is denoted R(i) but in Spring.Q uses real map. use restricted Cottage constant)
local notation "n₀"=> A.B.a.S.side m n
local notation "n₁"=> A.B.a.S.side (m+1) n
local notation "P"=> A.B.a.budget m
local notation "A!"=> A.B.a
local notation "J"=> A.B.a.clock.J (m+1)
local notation "T'"=> A.B.a.clock.J m
local notation "i!"=> (0:Site n₀)
local notation "β"=> Orchard.beam0
open UVNext.CouplingReset Mallow Lotus
variable (Y:ι→ RG.Rep G (A.B.a.S.side (m+1) n))(Q:(i:ι) → Spring R (t i) m n 0 1 (fun _=> Y i))(g:G.Simple)(hq:StableR v Y)
variable (M':(i:ι)→ Lotus.Leaf (Y i)) (hs : Wet.Constant (v:=v) M')
variable (p: Choir v (fun i=> Pane.orchestra A (t i) (A.B.a.S.oneStep m n|>.exact_size)) (shelter R Y Q) (A.B.a.budget m).order Chi.canonical)
variable (hR:Mallow.Arrives R.shape A.delay)(o:Site (A.B.a.S.side m n))(hy:∀ i,o∈ (M' i).crest.image (A.B.a.clock.op m n).ratio.parent)
namespace MarketP
open Graces Extra.Histories Source Labels Next.Foundations Planned.GuardedAtom Guard MergeProof Lacing Eyelet Rainfall
local notation "H₀"=> shelter R Y Q
set_option quotPrecheck false
variable (r:(i:ι)→Blush.Cloud (Y i)) (hd:Constant (v:=v) (fun i=>(r i).live))(hD:Constant (v:=v) (fun i=>(r i).pale)) (ht:∀ i,(0:Site (A.B.a.S.side m n))∈ (r i).live.crest.image (A.B.a.clock.op m n).ratio.parent)
    (hT:Tendsto (fun i=>(Q i).ordinal) v atTop)(K:∀ i:ι, Keeper ((Q i).result Orchard.beam0|>.p) ((Q i).result Orchard.beam0|>.activities)) -- notation variable!
local notation "L"=> D.L J
local notation "κ"=> Real.sqrt (A.B.a.clock.forcedAllowance m)
lemma tartan (d:ℕ)(i:ι) (Z:ℕ→ Support n₀) (h:Blush.scope (houseS (Q i) β) (r i) (0:Site n₀)=Z) : warp (p:=A.B.a.budget m) _ (Rainfall.wallet (K i) Z (localSection G d) (Rainfall.sky (Q i) β (((L).val:ℂ)^d) (r i) ((Labels.frames G).level d)) (hol G)) (hol G) κ (show ((Q i).result (β)).p=A.B.a.budget m from rfl) = Graces.tars (Q i) β (K i) (r i) d:=by subst Z; rfl
include g hm in
lemma wholesome(i:ι): ((Q i).result β).Lawful (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m):= ((Q i).moves g (hm i)).2 (β) (β).2 |>.1.bundle.valid
include h F U he hm hv hh hD hd hq ht hR g hT
lemma finance (d:ℕ)(j:ι): let M' i:= Rainfall.sky (Q i) β (((L).val:ℂ)^d) (r i) ((Labels.frames G).level d); let f i:= (Q i).result β; let Q0:= Blush.scope (H₀ j) (r j) (0:Site n₀)
    (∀ i,Blush.scope (houseS (Q i) β) (r i) (0:Site n₀)=Q0)∧ Cof (v:=v) (P) Q0 (fun i=> (M' i).bulk) ∧ Transit v (fun i j x=> (M' i).forced j x):=by
   intro M' f Q0; obtain ⟨T⟩:=Roads.Unum.fares R h F he hm hv hh (A.B.a.S.oneStep m n|>.exact_size) Y H₀
   let u:ℂ:= ((L).val:ℂ)^d
   have ht':= harsh R h F U he hm hv hh Y Q g hq _ hd T hR 0 ht hT j
   have hr':= harsh R h F U he hm hv hh Y Q g hq _ hD T hR 0 (fun i=> (r i).turnout ▸ ht i) hT j
   exact ⟨fun i=>scenes T hq r j hd i,panelsC T hq r j hd hD rfl (cooled R hm Y Q T hR) ht u, petals ((lofty ht'.joys).together (petals (lofty hr'.joys) Complex.I)) u⟩
lemma bingo (j:ι)(d:ℕ)(hn:∀ i,sparkT (Q i) β (r i) d): let M' i:= Rainfall.sky (Q i) β (((L).val:ℂ)^d) (r i) ((Labels.frames G).level d); let f i:= (Q i).result β; let Q0:= Blush.scope (H₀ j) (r j) (0:Site n₀)
    (∀ i, Valid (M' i) Q0 (f i) (A.B.a.clock.forcedAllowance m) (localSection G d) (hol G) (authors A.B.a m) κ):=by
   obtain ⟨ho,hQ,hF⟩:= finance R h F U he hm hv hh Y Q g hq hR r hd hD ht hT d j
   intro M' f Q0
   intro i; exact (show _= Q0 from ho i) ▸ hn i
lemma leafing (d:ℕ)(hX: Local.Readable (hol G) (localSection G d) P n₀ (authors A.B.a m))(hA:∀ i,sparkT (Q i) β (r i) d)(hr:∀ i,HasSlots ((Q i).result (β)).p ((Q i).result (β)).activities)(hc: Transit v (fun i j x=> ((Q i).result (β)).activities.K j x)) : ∃ z:Bucket ((Labels.frames G).level d) (P) (hol G) n₀,Tendsto (fun i=> (tars (Q i) β (K i) (r i) d : Bucket ((Labels.frames G).level d) (P) (hol G) n₀)) v (𝓝 z):=by
   let M' i:= Rainfall.sky (Q i) β (((L).val:ℂ)^d) (r i) ((Labels.frames G).level d); let f i:= (Q i).result β
   obtain ⟨j,-⟩:=(show ∀ᶠ i:ι in v, True from by simp).exists; let Q0:= Blush.scope (H₀ j) (r j) (0:Site n₀)
   obtain ⟨ho,hQ,hF⟩:= finance R h F U he hm hv hh Y Q g hq hR r hd hD ht hT d j
   let u:ℂ:=(↑(L|>.val):ℂ)^d
   have hp(i):(f i).p=(A.B.a.budget m):=rfl
   have hx (i α:ι): (f i).activities.forced=(f α).activities.forced:= (show _=Ovens.Pipes.addr (folio G _) P from (hr i).forced).trans (show _=Ovens.Pipes.addr (folio G _) P from (hr α).forced).symm
   obtain ⟨z,hZ⟩:= Wet.steadfast j (wholesome R hm Y Q g) hp (fun i=>hx i j) (Real.sqrt_pos.mpr (forcedPos _ _)) hc hX M' (bingo R h F U he hm hv hh Y Q g hq hR r hd hD ht hT j d hA) K hQ hF (fun _=>rfl)
   refine ⟨z,hZ.congr' (Eventually.of_forall (fun i=>tartan R Y Q r K d i _ (ho i)))⟩
end MarketP
end YM.UVExtension.Wet
