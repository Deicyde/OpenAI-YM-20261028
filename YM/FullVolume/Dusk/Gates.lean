import YM.FullVolume.Dusk.Law
import YM.FullVolume.Dusk.Evan
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
lemma peal (b:ℕ→Face T W) {n:ℕ}(x:Points n)(u:ℝ)(h:Tendsto (fun i=>evalV T W (b i) p i) atTop (𝓝 u))(hp:Eves.ancestor R.family.S x)(hv:x∈ NoHit R.family.S p n) (v:Fin n→R.family.book.Token): CauchySeq fun i=> ((b i).V T W).numeric i p v (Rising.robe L! p x i):= conic W H' hx (fun i=>(b i).score) (fun i=>(b i).owns) p n _ (fun i=> (v i).2) u h x hp hv
variable (h : Tendsto (fun i=> evalV T W P p i) atTop (𝓝 R.alloy.B.a.clock.bar))
include h
lemma pivotal {d n:ℕ} (x:Points n) (hp:Eves.ancestor R.family.S x)(hv:x∈ NoHit R.family.S p n)(w:ℕ→ Fin n→R.family.label d) (Z:ℝ)(hz:0≤Z)(ht:∀ i a, ‖w i a‖ ≤ Z) : Tendsto (fun i=> dist ((S').numeric i p (fun j=>⟨d,w i j⟩) (Rising.robe L! p x i)) (R.family.numeric i p (fun j=>⟨d,w i j⟩) (Rising.robe L! p x i))) atTop (𝓝 0):=by
    let Q(i):= Rising.robe L! p x i
    have ht0:Tendsto (fun i:ℕ=>evalV T W (centerF T W) p i) atTop (𝓝 β):= tendsto_const_nhds.congr' (Eventually.of_forall fun i=> (Face.unit p i).symm)
    let f (i:ℕ): MultilinearMap ℂ (fun _ : Fin n=>R.family.label d) ℂ:= (S').ensemble (N:=i) (p:=p) (fun _=>d) (Q i)
    let g (i:ℕ): MultilinearMap ℂ (fun _ : Fin n=>R.family.label d) ℂ:= R.family.ensemble (N:=i) (p:=p) (fun _=>d) (Q i)
    have hv (y:Fin n→R.family.label d): Tendsto (fun i=> (f i-g i) y) atTop (𝓝 0):=by
       have hz:= laurels (x:=fun i=>P) (y:=fun i=>centerF T W) (t:=fun i C=>evalV T W C p i) (fun (j:ℕ) (U:Face T W)=> (U.V T W).numeric j p (fun i=>⟨d,y i⟩) (Q j)) h ht0 (fun b h=>peal T W H' hx p b x _ h hp hv (fun i=>⟨d,y i⟩))
       simp_rw [dist_eq_norm] at hz; rw [tendsto_iff_norm_sub_tendsto_zero]; simp_rw [sub_zero]; exact hz
    have he: Tendsto (fun i=> (f i-g i) (w i)) atTop (𝓝 0):= militia (C:=R.family) d n _ w Z hz ht hv; simp_rw [dist_eq_norm]; rw [tendsto_iff_norm_sub_tendsto_zero] at he; simp_rw [sub_zero] at he; exact he
omit h hx H'
variable (S:Table R.family.book) (d:ℕ) (X:Columns R.family S d)
def roll : Columns (P.V T W) S d:=⟨X.dim,X.H,X.basis,X.realBasis,X.initial,X.amount,X.row,X.full⟩
variable (Z:X.Trials)
local notation "X'"=> (roll T W P S d X)
def deal :(roll T W P S d X).Trials:= ⟨Z.depth,Z.width,Z.window,Z.scale,Z.positive,Z.zoom,Z.mark,Z.lift,Z.later,Z.gap,Z.allowed,Z.small⟩ -- Z depends dims.X'
-- copy experiences.Odds.PhysicalD.only.C.St.Top.Cell.Funding.real anchors
variable (hq : ∀ q:ℕ,q≠p→∀ n:ℕ, Courant (((centerF T W).score.mat n q)) (P.score.mat n q)) (hp:Market.Purchases Z)
include h hq hp hx H'
lemma candles : VitalRank (deal T W P S d X Z) :=by
    let G':=deal T W P S d X Z; let F (k:ℕ) (i:Push.RelayDifference.Cutoffs) (j:Fin X.amount) (c:Fin (X.dim+1)):= FullVolume.monitor (siblings Z k j) i (Bid.upper R.family (boostsAt Z k c)) (loc Z k j i); let Gf k (i:Push.RelayDifference.Cutoffs) (j:Fin X.amount) (c:Fin (X.dim+1)):=FullVolume.monitor (siblings G' k (j:Fin (roll T W P S d X).amount)) i (Bid.upper (S') (boostsAt G' k (c:Fin ((roll T W P S d X).dim+1)))) (loc G' k _ i) -- annotation; ambig
    have hh:Booths (deal T W P S d X Z):= ⟨hp.bounded,hp.fit,hp.axis⟩; refine ⟨hh,fun ε he=>?_⟩
    have he(k:ℕ)(j:Fin X.amount)(c:Fin (X.dim+1)):∀ᶠ i in mesh, dist (Gf k i j c) (F k i j c)< ε/2 :=by
       let R':=S'; let a:= X.row j; let z:= Z.realPlace k j
       let m:=a.extra+1
       have hxA : Eves.ancestor R.family.S z:=by
          let v:ℕ:= Z.depth k; change Eves.ancestor _ (tag (R.family.S.a v) (Z.mark k j))
          exact ⟨v, congr_arg (tag (R.family.S.a v)) (address_matched (R.family.S.a_pos _) _).symm⟩
       obtain ⟨t,r,ht,hR,hX⟩:= arena Z (invested Z hp) k j
       have hf' := hX (Z.realPlace k j) (Metric.mem_closedBall_self ht.le) p
       have hxX: z∈NoHit R.family.S p m:=fun i j hij=>⟨timeAxis,fun ⟨s,hs⟩=>by
          have hp:= hf' j i hij.symm timeAxis s; unfold Gaps.distances at hp; rw [hs,dist_self] at hp; linarith only [hp,hR]⟩
       obtain ⟨y,hy⟩:= hp.bounded k
       let v(N q:ℕ)(i:Fin m):R.family.label d:= Fin.cons (α:=fun _ : Fin (a.extra+1)=> R.family.label d) (boostsAt Z k c (N,q)) (fun u=> wisps Z k j u (N,q)) i
       let ut N q:=fun i: Fin m=> (⟨d,v N q i⟩: R.family.book.Token)
       let L' (N q:ℕ):= loc Z k j (N,q)
       have hG N q: Gf k (N,q) j c= Extraction.lifted R' N q (ut N q) (L' N q):= FullVolume.ridge G' k (N,q) _ _ _
       have hF N q: F k (N,q) j c= Extraction.lifted R.family N q (ut N q) (L' N q):= FullVolume.ridge Z k (N,q) _ _ _
       have hL N (hk:Z.depth k≤ N): L' N p= Extraction.address (R.family.S.a N) z:=by
          have hv : Extraction.tag (R.family.S.a N) (L' N p)=z:= loc_tag Z k j (N,p) hk; exact (address_matched (R.family.S.a_pos _) _).symm.trans (congr_arg _ hv)
       have hw : ∀ N q i, ‖v N q i‖≤y:=fun N q i=> Fin.cases (hy N q c) (fun i=>hy N q _) i
       have hs:= Metric.tendsto_nhds.mp (pivotal T W H' hx P p h z hxA hxX (fun i=>v i p) y ((norm_nonneg _).trans (hy 0 0 c)) (fun i=>hw i p)) (ε/2) (half_pos he)
       rw [FullVolume.late]; filter_upwards [eventually_ge_atTop (Z.depth k), eventually_ge_atTop (R.family.ref d),hs] with N ht hk hv q
       rw [hG,hF]; by_cases hh:q=p
       · subst q; rw [Extraction.lifted,Extraction.lifted,hL N ht]; simp only [dist_zero_right,Real.norm_of_nonneg dist_nonneg] at hv; exact hv
       have hZ: Extraction.lifted R' N q (ut N q) (L' N q)= Extraction.lifted R.family N q (ut N q) (L' N q):=(gathered (centerF T W) P N q (hq q hh N) (ut N q) (fun i=>hk) (wrap _ ∘ L' N q)).symm; rw [hZ,dist_self]; exact half_pos he
    -- notation `he` shadow!
    filter_upwards [gaugesFull Z R.makes hp (ε/2) (half_pos (by assumption))] with k hk
    filter_upwards [hk,eventually_all.mpr (fun j=> eventually_all.mpr (fun c=> he k j c))] with i hi he j c
    change dist (Gf k i j c) (focus (X:=X) j c)<_
    exact lt_of_le_of_lt (dist_triangle _ (F k i j c) _) (add_halves ε ▸ add_lt_add (he j c) (hi j c)) -- arithmetic
end Face
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Face.candles
