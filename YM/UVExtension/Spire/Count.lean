import YM.UVExtension.Spire.Lodge
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Spire
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
variable {G : Gauge} {X: Metals G} {D:Rolls X.p} {A : Alloy X D} (R:Factor A)
    (hG:G.Simple){ε:ℝ}(t:Crest R ε)(u:Paperwork R.shape ε Camp.soft A.delay)
    (hk:Planned.Port.AtTop A.B.kin)(hp:∀ N,Start.Allows A.B.a N)(h:∀ N,Entry A.B.a N soft)(N n:ℕ)
open Cart
namespace Fitted
variable {R hG t hk hp N n} (H:Fitted R hG t hk hp N n)
    (V:Cart A.B.a N H.Hut)(he:H.Took V) {z:PlotN N}(hv:z∈Harbor N)(hZ: Cart.Light N z)
    {b:ℝ}
local notation "a!" => A.B.a
local notation "cN" => A.B.kin.alpha N
local notation "W#"=> H.W N

-- coords on centered real row
include hG
def lock (_R:Factor A) (z:PlotN N) (i:ℕ)(hi:i≤N):= Dales.art (A.B.a.clock.hatBeta i) (Camp.slope A.B.a (A.B.kin.alpha N) i) ((Cart.node N z i hi).re)
include hv
lemma locking (i)(hi:i≤N): lock R z i hi∈ RG.Shoot.band A.B.a i:= Camp.speaks _ _ (land (A:=A) hG N i hi) (Cart.parts N hv i hi)

-- every vector of β's real in roll gives a *strong* vector map, without having to witness a trajectory at those quantities. Even on plateaux.
open Cart
abbrev Home (i:ℕ):= Valve i n A.B.a (H.W i)

def file (z:PlotN N)(i:ℕ)(hi:i≤N): H.Home i := Nat.decreasingInduction (motive:=fun i _=> H.Home i) (fun i hi x=> Tour.choiceV R hG t (H.charts i hi) _ (H.shirts i hi) x (lock R z _ hi)) (Dales.singleA R (hp N) hk H.start (lock R z N le_rfl)) hi
lemma entry : file H z N le_rfl= city R (hp N) hk (locking (R:=R) (hG:=hG) hv N le_rfl) H.start:=by
   rw [file,Nat.decreasingInduction_self]; exact dif_pos (locking (R:=R) (hG:=hG) hv N le_rfl) -- hG & R infer
include hZ he

lemma officious (i:ℕ)(hi:i≤N): Reality A.B.a i n (H.W i) (H.file z i hi) (lock R z i hi) ∧ V.play a! N H.Hut z i hi=place a! i n (H.W i) (H.file z i hi):= by
   have hM i (hi:i≤N): RG.Rep.beta (mount R N i n 0 (lock R z i hi) 0)∈RG.Shoot.band A.B.a i:=locking (R:=R) (hG:=hG) hv i hi
   let x(i)(hi:i≤N):ℝ:= (Cart.node N z i hi).re
   have hz(i)(hi:i≤N):(↑(x i hi):ℂ)=Cart.node N z i hi:= by
     let p:= Cart.node N z i hi; have he:p.im=0:= hZ _; have h:=Complex.re_add_im p; rw [he] at h; simpa only [Complex.ofReal_zero,zero_mul,add_zero] using! h
   induction hi using Nat.decreasingInduction with
   | self=>
       let u:Flows a! N n (H.W N):=(x N le_rfl,0); let v:Flow a! N n (H.W N):=(Cart.node N z N le_rfl,0); let L:= river a! N n (H.W N); have hh:L u=v:= by apply Prod.ext; exact hz _ le_rfl; exact map_zero (place ..)
       have hg : v∈ Grip:= mem_ball_zero_iff.mpr (max_lt ((norm_le_pi_norm z _).trans_lt ((mem_closedBall_zero_iff.mp hv).trans_lt (by norm_num [rad,rim]))) (norm_zero.trans_lt (by norm_num [rim])))
       have hA := he.head.ray u (show _ from hh.symm ▸ hg); change V.headA (L u) = _ at hA; rw [hh] at hA
       rw [H.entry hv, V.roof]; refine ⟨attune R (hp N) hk _ H.start,?_⟩
       change _=place a! N n (H.W N) _; change V.headA v=_; rw [hA]; exact congr_arg (place a! N n (H.W N)) (show Dales.singleA R (hp N) hk H.start (lock R z N le_rfl)=_ from dif_pos (hM N le_rfl))
   | of_succ i hi ih=>
       let p:=pivot a! N H.Hut V z (i+1) hi; let L:= river a! (i+1) n (H.W (i+1)); let u:Flows a! (i+1) n (H.W (i+1)):=(x _ hi,H.file z (i+1) hi); have hh:L u=p:=Prod.ext (hz _ hi) ih.2.symm
       have hs: L u∈Grip:= hh ▸ (V.seats _ _ _ hv _ hi).2
       have ht := (he.phase i hi).ray u hs; change V.car i hi (L u)= _ at ht; rw [hh] at ht
       let w:= Tour.royals R hG t (H.charts i hi) _ ih.1 (H.shirts i hi)
       have hf : Tour.choiceV R hG t (H.charts i hi) _ (H.shirts i hi) (H.file z (i+1) hi) (lock R z _ hi)=w:= dif_pos ih.1
       rw [show H.file z _ hi.le=w from Eq.trans (Nat.decreasingInduction_succ_left _ _ hi hi.le) hf, edge _ N _ _ z i hi]; exact ⟨⟨hM i hi.le, Tour.new_mem R hG t _ _ ih.1 _⟩,ht.trans (congr_arg (place _ _ _ _) hf)⟩
lemma bonusR (i:ℕ)(hi:i<N): V.tally a! N H.Hut z i=↑(Tour.bonus R (H.charts i hi) _ (H.officious V he hv hZ (i+1) hi).1):= by
   have hh:= H.officious V he hv hZ (i+1) hi; let p:=Cart.node N z (i+1) hi; let q:= ((p.re,H.file z _ hi):Flows a! (i+1) n (H.W (i+1)))
   have hx: V.pivot a! N H.Hut z (i+1) hi= river a! (i+1) n (H.W (i+1)) q:= by
      apply Prod.ext; · have he:=Complex.re_add_im p; rw [show p.im=0 from hZ _, Complex.ofReal_zero,zero_mul,add_zero] at he; exact he.symm
      exact hh.2
   rw [Cart.tally,dif_pos hi,hx, (he.pigment i hi).ray q (hx ▸ (V.seats _ _ _ hv _ hi).2)]
   exact congr_arg Complex.ofReal (show Tour.claim R (H.charts i hi) _ _ _=_ from dif_pos hh.1)

omit hv hZ
variable (hf:Fees A.B.a)(hh:(↑b:ℂ)∈Broad A.B.a)
include he hh
lemma blessed : Cart.Light N (V.picked hG a! N H.Hut hf (b:= (b:ℂ))):=by
   apply Cart.gilded hG a! N H.Hut V hf hh rfl; intro z hv hZ i; by_cases hi:i<N
   · rw [H.bonusR V he hv hZ i hi]; rfl
   unfold Cart.tally; rw [dif_neg hi]; rfl
end Fitted
end YM.UVExtension.Spire
#print axioms YM.UVExtension.Spire.Fitted.blessed
