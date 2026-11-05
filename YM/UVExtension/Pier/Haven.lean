import YM.UVExtension.Pier.Loom
import YM.UVExtension.Crown.Tab
import YM.UVExtension.Orchard.Racks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
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
open Guild Tabernacle Spire Orchard
open Dales Camp Whirl Oriel Oriel.Charted Tour Above Tabernacle WilsonStartup
open Cart Linden Willow Bud Mallow Daisy Daisy.Charity Fitted
variable {G : Gauge} {hG:G.Simple}{X: Metals G} {D:Rolls X.p} {A : Alloy X D} {R:Factor A} (S: Uses R hG)
    (N n m:ℕ)
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "H"=> S.fits N n
local notation "V"=> S.cart N n
local notation "F"=> S.grove.coins
variable (v:Rose S)
lemma poss (hm:m≤N): HasSlots (S.realBeat v.val N n m).p (S.realBeat v.val N n m).activities:=by
    have h:= H|>.acts V (S.token N n) F v.2; exact (H).protector (r:=0) (s:=(H).Sail (V) (F) v.val) ⟨Nat.zero_le _,fun i _=>h.1.alive i,h.1.bare, fun i _=>h.1.passes i⟩ m (Nat.zero_le _) hm
lemma liveR (hm:m≤N): let X:=S.realBeat v.val N n m; let s:=A.B.a.params m; let w:=A.B.a.clock; X.Lawful s.width s.paths (w.loopCap m) (w.allowance m) (w.forcedAllowance m):= ((S.ticking N n v.2).prices m (Nat.zero_le _) hm).1.valid
variable {a:ℝ}(ha:0<a)(hp:ball (0:ℂ) a ⊆ Camp.Broad A.B.a)
set_option quotPrecheck false
local notation "T"=> desk a ha
local notation "Y"=> Row a
def roseK (d:Row a):Rose S:=⟨d.val,hp ((desk a ha).within d)⟩
abbrev Point (b:ℂ)(i:ℕ)(hi:i≤N):= pivot a! N (S.fits N n).Hut (V) (sonnet (H) (V) (F) b) i hi
noncomputable abbrev starZ (b:ℝ)(i:ℕ)(hi:i≤N):Flows a! i n ((S.fits N n).W i):= ((node N (sonnet (H) (V) (F) (b:ℂ)) i hi).re,(H).Rest V F b i)
variable (hm:m<N)
include hp
lemma northern (b:Y)(h:m≤N): Point S N n ((T).call b) m h=river a! m n ((H).W m) (starZ S N n b.val m h):=by
    have hh:= H|>.really V (S.token N n) F (hp ((desk a ha).within b)) m h; let p:=node N (sonnet (H) (V) (F) (b.val:ℂ)) m h; refine Prod.ext ?_ hh.2
    have he:=Complex.re_add_im p; rw [show p.im=0 from (H|>.blessed V (S.token N n) F (hp ((T).within b))) _, Complex.ofReal_zero,zero_mul,add_zero] at he; exact he.symm
lemma embarked (h:m≤ N): Set.MapsTo (fun b:ℂ=>Point S N n b m h) ((T).span) Grip ∧ Bumps (T).span (fun b:ℂ=>Point S N n b m h):=by
    have he : DifferentiableOn ℂ (fun b=>Point S N n b m h) (Camp.Broad a!) := ((nodded (H) (V) (F) m h).prodMk (riversV (H) (V) (F) m h).1)
    exact ⟨fun z hz=> ((V).seats _ N _ ((H).glint V F z (hp hz)) m h).2, bumps _ _ (he.mono hp)⟩
local notation "s0"=> shrine S m N n hm
noncomputable abbrev cents (d:Row a):= ray S N n m (roseK S ha hp d) hm -- Δ
local notation "O"=> Chi.canonical
local notation "ψ0"=> A.B.a.clock.hatBeta (m+1)
local notation "X0"=> mount R N (m+1) n 0 ψ0 0
local notation "Δ"=> (S.fits N n).W (m+1)
set_option quotPrecheck false
noncomputable abbrev fleetK (d:Row a)(i:Set.Icc (0:ℝ) 1):= Dales.ties (u:=starZ S N n d.val (m+1) hm) R (shrine S m N n hm) Δ (((H).acts V (S.token N n) F ((roseK S ha hp d).2)).1.alive (m+1) hm) (cents S N n m ha hp hm d) i
local notation "J"=> Cash.fragrances (shrine S m N n hm).atTopH
variable (M: Lotus.Leaf (mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0))(hM: Guarded R M)
   (M':(b:Row a)→ Lotus.Leaf (S.realBeat b.val N n (m+1)))(hμ:∀ b,(M' b).turn=M.turn)(hr:∀ b,(M' b).ingredient=M.ingredient)
   (b:Row a) (i:Set.Icc (0:ℝ) 1) (y:Site (A.B.a.S.side m n))
include hr hμ
local notation "Γ"=> Camp.slope a! cN (m+1)
local notation "X1"=> fun b:Row a=> cents S N n m ha hp hm b
local notation "Ω"=> fun b:Row a=> fleetK S N n m ha hp hm b i
local notation "ϖ"=> A.B.a.budget m
noncomputable abbrev mart (i:Set.Icc (0:ℝ) 1)(b:Row a) (j:J):= matin (M' b) (houseS (cents S N n m ha hp hm b).body i) ((fleetK S N n m ha hp hm b i).furrow j) Chi.canonical
set_option maxHeartbeats 500000 in
lemma paysV : let V':= starZ S N n b.val (m+1) hm; let W:= X1 b
   (∀ j:J,toast R s0 Δ M hM Γ V' j= mart S N n m ha hp hm M' i b j) ∧ drink R s0 Δ M hM Γ V'= pupil W.body i (M' b):=by
   intro v' W; have h:= H|>.acts V (S.token N n) F (roseK S ha hp b|>.2); have he:(H).Third V F b.val (m+1)=whenSt Δ Γ v':=dif_pos (show m+1≤N from hm)
   exact Dales.prints (u:=starZ S N n b.val (m+1) hm) R s0 Δ M hM (h.1.alive _ hm) (poss S N n (m+1) (roseK S ha hp b) hm) he (M' b) (hμ _) (hr _) W i
omit hr
lemma bray (j:J): locus (M' b) (houseS ((X1 b).body) i) y ((Ω b).furrow j)=locus M (s0).atTopH y j := Dales.lovelyCone (u:=starZ S N n b.val (m+1) hm) R s0 Δ M (((H).acts V (S.token N n) F ((roseK S ha hp b).2)).1.alive _ hm) (M' b) (hμ b) (X1 b) i y j
include hr
-- π output, +2 margin erased.P.C.We. atlas budget.
variable (k:ℕ)(he:y∈M.crest.image (A.B.a.clock.op m n).ratio.parent) (hk:Guild.PriceS R m)
open Rafter Copse
include he hk hM
set_option quotPrecheck false
set_option maxHeartbeats 500000 in
lemma capital:
   let b:=2*budgetsP M (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) k;
   let X:= locus M (s0).atTopH y
   Stalk (nose X k (ϖ).B (ϖ).supportExponent) (T) (fun (d:Row a) j x=> ((masked (ϖ).threshold (X j) (mart S N n m ha hp hm M' i d j) x:ℝ):ℂ)) b ∧ Stalk (mantleX A m n k) T (fun (d:Row a) j x=> ((tonic (pupil (X1 d).body i (M' d)) j x:ℝ):ℂ)) b:=by
   intro b X; let v(d:Row a):= starZ S N n d.val (m+1) hm; have ht:= embarked S N n (m+1) ha hp hm; have hc:= Spire.land (A:=A) hG N (m+1) hm
   obtain ⟨-,⟨hR⟩,⟨hK⟩⟩:= Dales.opened R hG S.grove.pledge (s0) (Δ) hk S.grove.enabled hc M hM y he T k _ v (fun i=>northern S N n (m+1) ha hp i hm) ht.2 ht.1
   have h₀(d):= paysV S N n m ha hp hm M hM M' hμ hr d i; constructor
   · let s (d:Row a)(j:J):= masked (ϖ).threshold (X j) (mart S N n m ha hp hm M' i d j); obtain ⟨P₀⟩:= Copse.diminishing k (ϖ).B (show (ϖ).supportExponent ≤ (ϖ).supportExponent+2 by linarith) X (fun _=> Config G (A.B.a.S.side m n)) hR
     have h: s= masksT R s0 Δ M hM y Γ∘v:=by
        funext d j; exact congr_arg (fun t:Config G (A.B.a.S.side m n)→ ℝ=> masked (ϖ).threshold (X j) t) ((h₀ d).1 j|>.symm)
     change Stalk (nose (G:=G) X k (ϖ).B (ϖ).supportExponent) (desk a ha) (fun d j x=> ↑(s d j x)) b; rw [h]; exact (Stalk.ascend P₀).eases (le_of_eq (two_mul _).symm)
   let p (d:Row a):= Mallow.tonic (pupil (X1 d).body i (M' d)); have hh: earsP R s0 Δ M hM Γ ∘ v=p:=by
     funext d j x; exact congr_arg (fun t=> deriv (fun z=> t z j x) 0) (h₀ d).2
   change Stalk (mantleX A m n k) (desk a ha) (fun d j x=> ↑(p d j x)) b; rw [←hh]; exact (Stalk.ascend hK).eases (le_of_eq (two_mul _).symm)
end YM.UVExtension.Pier
