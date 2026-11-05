import YM.FullVolume.Dusk.Court
import YM.FullVolume.Dusk.Gates
import YM.FullVolume.Literal
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Campaign
open Function Filter Set MeasureTheory Lattice RG RG.Supply Wilson Precision Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Mallow Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open YM.MergeProof
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp
open Pillars Bandage Pass Muse Contest Ovens
variable {R:Run G} (T:Campaign R)
set_option quotPrecheck false
local notation "L!"=> R.alloy.B.a
local notation "K!"=> R.alloy.B
local notation "o"=> R.alloy.B.a.clock.bar
open Spirit Branch
open Boutique
open Extraction Extraction.Lease
variable (W: Pillars R T)
-- Diagram frame physical labels.Select.Stream REAL and branch.
namespace Face
open Filter Set Function MeasureTheory Metric Extraction Extraction.Lease Difference YM.FullVolume.Dusk Next.Extract MergeProof Cells Next.Rank
open Market
variable (H':T.Winter) (hx:Jams.Wild R.kit.shape R.alloy.delay)
local notation "C₁"=> centerF T W
variable (P:Face T W)(p:ℕ)
local notation "β"=> R.alloy.B.a.clock.bar
local notation "S'"=> P.V T W
local notation "R₀"=> R.family
include H' hx
open FullVolume Push.RelayDifference
variable (h : Tendsto (fun i=> evalV T W P p i) atTop (𝓝 R.alloy.B.a.clock.bar))
variable (hq : ∀ q:ℕ,q≠p→∀ n:ℕ, Courant (((centerF T W).score.mat n q)) (P.score.mat n q))
include h hq
lemma carriage (n:ℕ)(v:Fin n→R.family.book.Token)(l:List (MotionIndex n))(r:ℝ)(hr:0<r): ∃ B:ℝ,0 ≤ B ∧ ∀ᶠ i in atTop,∀ x:Positions n, spaceout R.family r (i,p) (wrap _ ∘ x) → ‖gKernel (P.V T W) v l i p x‖ ≤ B:=by -- hQ needed
   obtain ⟨s,hs,hx⟩:= (pinnacle T W H' hx P p h hq).bounds n v l r hr; exact ⟨s,hs,hx.mono fun i hi=> hi p⟩
omit h hq H' hx
open Classical in
lemma peeling (A:ℕ→Face T W) (he:∀ n:ℕ, |evalV T W (A n) p n- R.alloy.B.a.clock.bar| ≤ outing T p): ∃ B:Face T W, (∀ N:ℕ,B.F p N=(A N).F p N)∧ (∀ N, Courant ((A N).score.mat N p) (B.score.mat N p)) ∧ ∀ q:ℕ,q ≠ p →∀ n:ℕ,Courant (((centerF T W).score.mat n q)) (B.score.mat n q):=by
    let f q i:= if q=p then A i else centerF T W
    have hz q n: |evalV T W (f q n) q n - R.alloy.B.a.clock.bar|≤ outing T q:=by
       by_cases h:q=p; subst q; simp only [f,if_pos rfl,he n]; simp only [f,if_neg h, Face.unit, sub_self,abs_zero]; exact (allowed ..).le
    obtain ⟨U,hU,hZ⟩:= selectedG f hz; exact ⟨U,fun N=> (hU p N).trans (by simp [f]),fun N=> (show f p N=A N from if_pos rfl) ▸ hZ p N,fun q h n=> (show f q n=centerF T W from if_neg h) ▸ hZ q n⟩
lemma corn {n:ℕ}(l:List (MotionIndex n))(v:Fin n→R.family.book.Token) (A:ℕ→Face T W)(U:Face T W)(ha:∀ N,Courant ((A N).score.mat N p) (U.score.mat N p)) : ∀ᶠ i:ℕ in atTop, gKernel (V T W (A i)) v l i p=gKernel (V T W U) v l i p:=by
    filter_upwards [eventually_all.mpr (fun j:Fin n=> eventually_ge_atTop (R.family.ref (v j).1))] with N hi
    have he: Extraction.lifted (V T W (A N)) N p v= Extraction.lifted (V T W U) N p v:= funext fun x=> gathered (A N) U N p (ha N) v hi _
    unfold gKernel; exact congr_arg (deltas _ _) he
include H' hx
variable (n:ℕ)(v:Fin n→ R.family.book.Token)(l:List (MotionIndex n))(r:ℝ)(hr:0<r)
include hr
lemma tallish (A:ℕ→ Face T W)(he:Tendsto (fun i=> evalV T W (A i) p i) atTop (𝓝 R.alloy.B.a.clock.bar))(hv:∀ N:ℕ,|evalV T W (A N) p N-R.alloy.B.a.clock.bar| ≤ outing T p):∃ B:ℝ, 0≤ B ∧ ∀ᶠ N in atTop,∀ x:Positions n, spaceout R.family r (N,p) (wrap _ ∘ x)→‖gKernel (V T W (A N)) v l N p x‖ ≤ B:=by
   obtain ⟨Q,H,hC,hq⟩:= peeling T W p A hv; obtain ⟨B,hB,hR⟩:= carriage T W H' hx Q p (he.congr' (Eventually.of_forall fun i=> (congr_arg bonusB (H i)).symm)) hq n v l r hr; refine ⟨B,hB,?_⟩; filter_upwards [corn T W p l v A Q hC,hR] with i hi hx; rw [hi]; exact hx

/-- Here near-uniformity in the parameter, **all-volume only after fixing p**, and all near histories INCLUDING normalization. Rebasing m=0 retained solely as bookkeeping. -/
lemma headlands : ∀ᶠ c in 𝓝[>] (0:ℝ), ∃ B:ℝ, 0≤B ∧ ∀ᶠ N in atTop,∀ P:Face T W,
     |evalV T W P p N-R.alloy.B.a.clock.bar|≤ c → ∀ x:Positions n,spaceout R.family r (N,p) (wrap _ ∘ x) → ‖gKernel (V T W P) v l N p x‖ ≤ B:=by
   let Z(c:ℝ)(N:ℕ)(P:Face T W):=|evalV T W P p N-β|≤c
   let L(N:ℕ)(x:Positions n):=spaceout R.family r (N,p) (wrap _ ∘ x)
   let x' (N:ℕ)(P:Face T W)(x:Positions n):= ‖gKernel (V T W P) v l N p x‖
   let Q(c:ℝ)(B:ℝ):Prop:=∀ᶠ N in atTop,∀ P:Face T W,Z c N P → ∀ x:Positions n,L N x→x' N P x≤ B
   have hf : ∃ c:ℝ,0 < c ∧ ∃ B:ℝ,0≤B∧ Q c B:=by
       by_contra hn; push_neg at hn
       obtain ⟨g,hg,h,hS⟩:= exists_seq_strictAnti_tendsto (0:ℝ) -- likely conjunction order
       let f(i):= min (outing T p) (g i)
       have hx':∀ i,0<f i:=fun i=> lt_min (allowed ..) (h i)
       have hh: ∀ i:ℕ,∀ a:ℕ, ∃ N:ℕ,a<N ∧ ∃ (P:Face T W) (x:Positions n),Z (f i) N P ∧ L N x∧ i < x' N P x :=by
          intro i a; obtain ⟨N,H,h⟩:= ((not_eventually.mp (hn (f i) (hx' i) (i:ℝ) (by positivity))).and_eventually (eventually_gt_atTop a)).exists; push_neg at H
          obtain ⟨A,ha,v,hT,hv⟩:=H; exact ⟨N,h,A,v,ha,hT,hv⟩ -- check push_neg hn includes Frequently
       choose K hK t ht hA hu hD using hh
       let a:ℕ→ℕ:=fun i=> Nat.rec 0 (fun i j=> K i j) i
       have ha(i): a (i+1)=K i (a i):= by simp [a]
       let b(i):=K i (a i); have hb(i): b i=a (i+1):=(ha i).symm
       have hB:StrictMono b:= strictMono_nat_of_lt_succ (fun i=> by rw [hb i]; exact hK (i+1) (a (i+1)))
       let S:ℕ→ Face T W:= extend b (fun i=>t i (a i)) (fun _=>centerF T W)
       have hz (i): S (b i)=t i (a i):= hB.injective.extend_apply _ _ _
       have ht₀(N): |evalV T W (S N) p N - β|≤ outing T p:= by
          by_cases hc:N∈ range b
          · obtain ⟨i,rfl⟩:=hc; rw [hz]; exact (hA i (a i)).trans (min_le_left ..)
          rw [show S N=_ from extend_apply' _ _ _ hc, Face.unit,sub_self,abs_zero]; exact (allowed ..).le
       have hv : Tendsto (fun i=> evalV T W (S i) p i) atTop (𝓝 β):=by
          rw [Metric.tendsto_nhds]; intro ε he; obtain ⟨N,hN⟩:= eventually_atTop.mp (hS.eventually (gt_mem_nhds he))
          filter_upwards [eventually_ge_atTop (b N)] with i hi; by_cases h:i∈range b
          · obtain ⟨i,rfl⟩:= h; rw [Real.dist_eq,hz]; exact ((hA i (a i)).trans (min_le_right ..)).trans_lt (hN i (hB.le_iff_le.mp hi))
          rw [show S i=_ from extend_apply' _ _ _ h, Face.unit,dist_self]; exact he
       obtain ⟨B,hb',h'⟩:= tallish T W H' hx p n v l r hr S hv ht₀
       obtain ⟨i,hv,h⟩:= ((tendsto_natCast_atTop_atTop.eventually_ge_atTop B).and (hB.tendsto_atTop.eventually h')).exists
       have he:= hD i (a i)
       refine not_lt_of_ge ((?_ : x' (K i (a i)) _ _ ≤ B).trans hv) he
       change x' (b i) _ _ ≤ B
       rw [← hz]; exact h _ (hu i _)
   obtain ⟨y,hy,a,ha,hZ⟩:=hf; filter_upwards [eventually_nhdsWithin_of_eventually_nhds (ge_mem_nhds hy)] with c hc; exact ⟨a,ha,hZ.mono fun i hi p hp=> hi p (hp.trans hc)⟩
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.headlands
