import YM.UVExtension.Pier.Haven
import YM.UVExtension.Pier.Grind
/-! # Local dual step. Both log and marked gas push in SAME windows. -/
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
    (N n m:ℕ) {a p:ℝ}(ha:0<a)(hp:ball (0:ℂ) a ⊆ Camp.Broad A.B.a) (hm:m<N)
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "T"=> desk a ha
local notation "Y"=> Row a
local notation "s0"=> shrine S m N n hm
set_option quotPrecheck false
local notation "V'"=>fun (b:Row a) i=> S.realBeat b.val N n i
set_option quotPrecheck false
local notation "J"=> Cash.fragrances (shrine S m N n hm).atTopH
variable (M: Lotus.Leaf (mount R N (m+1) n 0 (A.B.a.clock.hatBeta (m+1)) 0))(hM: Guarded R M)
   (M':(b:Row a)→ Lotus.Leaf (S.realBeat b.val N n (m+1)))(hμ:∀ b,(M' b).turn=M.turn)(hr:∀ b,(M' b).ingredient=M.ingredient)
   (b:Row a)
local notation "X1"=> fun b:Row a=> cents S N n m ha hp hm b
local notation "i!"=> Orchard.beam0
local notation "τ"=> A.B.a.clock.op m n
local notation "ϖ"=> A.B.a.budget m
local notation "Xo"=> (0:Site (A.B.a.S.side m n))
variable (k:ℕ)(he:(0:Site (A.B.a.S.side m n)) ∈M.crest.image (A.B.a.clock.op m n).ratio.parent) (hk:Guild.PriceS R m)
open Rafter Copse Lotus
variable (h: Mallow.Arrives R.shape A.delay)
include he
local notation "n₀"=> A.B.a.S.side m n
local notation "X'"=> locus M (s0).atTopH Xo
local notation "E₀"=> Address X' (seatY M (s0).atTopH (Xo) he)
local notation "L₀"=> Wing.gasKey
local notation "f"=> fun (b:Row a) (j:Cash.fragrances (shrine S m N n hm).atTopH) => Complex.ofReal ∘ masked (ϖ).threshold (locus M (s0).atTopH Xo j) (mart S N n m ha hp hm M' i! b j)
local notation "p'"=> fun (b:Row a)=> Mallow.nectar (pupil (X1 b).body i! (M' b))
local notation "ρ"=> 2*budgetsP M (R.target (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)) k
include hk he hμ hM hr
lemma flask : Stalk (nose (G:=G) (land G n₀ ϖ ∘ (E₀)) k (ϖ).B (ϖ).supportExponent) T (f) ρ∧ Stalk (nose (G:=G) (land G n₀ ϖ ∘ L₀) k (ϖ).B (ϖ).supportExponent) T p' ρ:=by
   obtain ⟨hs,h⟩:= capital S N n m ha hp hm M hM M' hμ hr i! (Xo) k he hk; refine ⟨?_, h⟩
   have hzz: land G n₀ ϖ ∘ E₀=X':=by
     funext j; exact stamp _ _ (Q:=S.realBeat 0 N n m) rfl (poss S N n m (rose0 S) hm.le)
   exact (congr_arg (fun X: J→ Support n₀=> Stalk (nose (G:=G) X k (ϖ).B (ϖ).supportExponent) T (fun b j=>f b j) ρ) hzz.symm) ▸ (show Stalk (nose (G:=G) (locus M (s0).atTopH Xo) k (ϖ).B (ϖ).supportExponent) T (fun b j=>f b j) ρ from hs)
omit hk hM hr
include h
-- real regrouping uses Stir and Equation supports. proofs via any single ray.
set_option quotPrecheck false
lemma bran (hV:Dominated (f b)) (hT:Dominated (p' b)): (∀ i,Held ϖ (E₀ i) (f b i)) ∧ (∀ i,Held ϖ (.gasKey i) (p' b i)) ∧ (τ).push ((V' b (m+1)).beta) (Complex.ofReal ∘ (M' b).cicada) =(fun U:Config G (n₀)=> ∑' i, port (V' b m) (E₀ i) U * f b i U)+(fun U=>∑' i,port (V' b m) (.gasKey i) U * p' b i U):=by
    let Q:= roseK S ha hp b; let v:= S.realBeat Q.val N n; have he': v m=(X1 b).body.result i! := ponds ..
    have hM : M.crest=(M' b).crest:= (show M.crest=land G (A.B.a.S.side (m+1) n) (A.B.a.budget (m+1)) M.turn from whereAt M.turn rfl ⟨rfl,rfl,fun _=>rfl,fun _=>rfl⟩).trans ?_
    · obtain ⟨h1,h₂,hQ⟩:= swept hG hm (X1 b).body i! ((fleetK S N n m ha hp hm b i!).furrow) (M' b) X' (fun i=> bray S N n m ha hp hm M M' hμ b i! (Xo) i) (seatY M (s0).atTopH (Xo) he) h (hM ▸ he) (show HasSlots _ _ from show HasSlots ϖ ((X1 b).body.result i!).activities from he' ▸ (show HasSlots ϖ (v m).activities from poss S N n m Q hm.le)) (f b) (fun _=>rfl) hV hT
      refine ⟨h1,h₂,?_⟩
      let G' (x:Rep G (A.B.a.S.side m n)):= (fun U:Config G (n₀)=> ∑' i, port x (E₀ i) U * f b i U)+(fun U=>∑' i,port x (.gasKey i) U * p' b i U)
      have hu: Complex.ofReal ∘ (τ).push (v (m+1)).beta (M' b).cicada = G' (v m):= hQ.trans (congr_arg G' he'.symm); exact (funext (fun i=>Blush.Cloud.painted (τ) ((V' b (m+1)).beta) i ((M' b).cicada))).trans hu
    exact (congr_arg (land G (A.B.a.S.side (m+1) n) (A.B.a.budget (m+1))) (hμ b|>.symm)).trans ((whereAt (Q:=v (m+1)) (M' b).turn rfl (poss S N n (m+1) Q hm)).symm)
include he hk hM hr h
variable (hx:0≤p)(ht:Harbour (desk a ha) k (A.B.a.budget m) (fun b:Row a=> S.realBeat b.val N n m) p)
include hx ht hp hm
lemma hauls : Pier.Sail T (fun b:Y=> Pier.total (V' b (m+1)) (Complex.ofReal ∘ (M' b).cicada)) (p*ρ+p*ρ):= by
   let V(b:Y):= V' b m; have hv(d:Y):= liveR S N n m (roseK S ha hp d) hm.le
   obtain ⟨hE,hK⟩:= flask S N n m ha hp hm M hM M' hμ hr k he hk
   have hC b:=accounted T k f E₀ hE b; have hP b:=accounted T k p' L₀ hK b; let X(b:Y):= ∑' i, hit (V b) (E₀ i) (f b i); let Z (b:Y):= ∑' i, hit (V b) (L₀ i) (p' b i); have he'(b:Y):=bran S N n m ha hp hm M M' hμ b he h (hC b) (hP b)
   have hA : 0≤ ρ:= mul_nonneg zero_le_two (mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le (mul_nonneg M.profit (Real.exp_pos _).le)))
   have hX:= traders T V hv k f E₀ ht hx hE hA (fun i=> Pier.letter ϖ (X' i) _) (fun b=> (he' b).1); have hZ:= traders T V hv k p' L₀ ht hx hK hA (fun i=> Pier.gas ϖ _) (fun b=> (he' b).2.1); refine (Eq.symm (show (fun b:Y=> Pier.total (V' b (m+1)) (Complex.ofReal ∘ (M' b).cicada))= (fun b=>X b+Z b) from ?_)) ▸ Sail.plus hX hZ
   funext b; obtain ⟨h₁,h₂,hB⟩:=he' b; let z:=roseK S ha hp b; have hz:= liveR S N n (m+1) z hm; have hp' : Integrable (Complex.ofReal ∘ (M' b).cicada) (prior G (A.B.a.S.side (m+1) n)):= ((M' b).sells hz|>.1.integrable _).ofReal
   have hG := S.ticking N n z.2; rw [transmute (V' b (m+1)) hz (τ) (a!|>.transition_mass ..) (V b) ((hG.persists m (Nat.zero_le _) hm).link) (Complex.ofReal ∘ (M' b).cicada) hp',hB, sums (V b) ((recorded E₀ (V b) (hv b) (f b) (hC b) (fun i=> (h₁ i).mesh)).integrableC _) ((recorded L₀ (V b) (hv b) (p' b) (hP b) (fun i=> (h₂ i).mesh)).integrableC _)]
   exact congr_arg₂ (·+·) ((stored E₀ (V b) (hv b) (f b) (hC b) (fun i=> (h₁ i).mesh)).tsum_eq).symm ((stored L₀ (V b) (hv b) (p' b) (hP b) (fun i=> (h₂ i).mesh)).tsum_eq).symm
end YM.UVExtension.Pier
