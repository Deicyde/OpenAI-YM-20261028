import YM.UVExtension.Spire.Thrill
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
variable {f: ∀ i, H.Home i}{β:ℕ→ℝ}{s:ℕ→ℝ}(hs:Shot H f β s)
    (hb: (↑b:ℂ)∈ Camp.Broad A.B.a)(hr:β 0=A.B.a.clock.bar+b)
include hs
lemma top_mom : f N=city R (hp N) hk (hs.alive N le_rfl).1 H.start:= by
    let Y:= city R (hp N) hk (hs.alive N le_rfl).1 H.start; exact Subtype.ext (congr_arg (fun x=> (x.activities.E,x.activities.K)) hs.bare)
include u h hb hr
omit u h in
lemma rootc (m:ℕ)(hm:m≤N) : InsideB (A.B.a.clock.hatBeta m) (β m):= by
    apply Camp.known hG a! (RG.Shoot.Drifting.pay A.B.valid) (β:=β) _ _ hm
    · rw [hr,add_sub_cancel_left]; have hv:=mem_ball_zero_iff.mp hb; rw [Complex.norm_real] at hv; exact hv.le
    intro i hi; exact (A.B.links hi (H.serves hs i hi|>.1)).drift

lemma plates (m:ℕ)(hm:m≤N): ‖place a! m n (H.W m) (f m)‖≤ Camp.soft ∧ ∀ ht:m<N, |Tour.bonus R (H.charts m ht) _ (hs.alive _ ht)| ≤ worth a! (m+1):= by
    induction hm using Nat.decreasingInduction with
    | self=>
       rw [H.top_mom hs]; refine ⟨?_,fun hg=>False.elim (lt_irrefl _ hg)⟩
       have hw:= fundedP N a!
       refine (Tabernacle.tickP (A.B.a.budget N) _ _ hw.1 hw.2 ((H.W N).income _ (city R (hp N) hk (hs.alive N le_rfl).1 H.start)|>.1)).2 ?_
       exact (billT n (hp N) (h N) (hs.alive N le_rfl).1).gates (A.B.kin.path N N) (A.B.a.params N).clip (β N) 0 -- uw
    | of_succ i hi ih=>
       let d:= H.W (i+1); let L:= river a! (i+1) n d; let q: Flows a! (i+1) n d:= (0,f (i+1)); let J:= H.charts i hi; let v:= H.W i
       have hp: L q∈ Grip:= by refine mem_ball_zero_iff.mpr ?_; exact max_lt (show ‖(0:ℂ)‖<rim by norm_num [rim]) (ih.1.trans_lt (by norm_num [Camp.soft,rim]))
       let x:=β (i+1); obtain ⟨⟨Y,hY⟩,⟨Z,hZ⟩⟩:= Dales.shelves R hG t (H.charts i hi) (H.W (i+1)) u (H.rootc hs hb hr _ hi) (H.shirts i hi)
       have hz: art (A.B.a.clock.hatBeta (i+1)) x q.1=x:= by change _+_*0=_; ring;
       have hA : Tour.choiceV R hG t J _ (H.shirts i hi) q.2 (art (A.B.a.clock.hatBeta (i+1)) x q.1)=f i:= by rw [hz,Tour.choiceV,dif_pos (show Reality a! (i+1) n (H.W (i+1)) q.2 x from hs.alive _ hi)]; exact (H.doors hs i hi).2.1.symm
       have hQ: (flowing R J _ x q)=↑(Tour.bonus R J _ (hs.alive _ hi)):= by unfold Dales.flowing; rw [hz,Tour.claim,dif_pos (show Reality a! (i+1) n (H.W (i+1)) q.2 x from hs.alive _ hi)]
       have heq : Z (L q)= place a! i n (H.W i) (f i):= (hZ.ray q hp).trans (congr_arg (place a! i n v) hA)
       have hv := (hY.bounds.2.1 (L q) hp); have hg : Y (L q)=↑(Tour.bonus R J _ (hs.alive _ hi)) := (hY.ray q hp).trans hQ
       exact ⟨heq ▸ hZ.bounds.2.1 _ hp,fun hi=>by rw [hg,Complex.norm_real] at hv; exact hv⟩

variable (hf:Fees A.B.a)
-- attach beta trial chart
include he hf
def cut (_R:Factor A)(N:ℕ)(β:ℕ→ℝ)(i:ℕ): ℝ:= (β i - Camp.slope a! (A.B.kin.alpha N) i)/Camp.pulse a! i
def port (R:Factor A)(N:ℕ)(β:ℕ→ℝ) : PlotN N:= fun i=>↑(cut R N β i.val)

omit he in
lemma pivots : port R N β ∈ Harbor N:=by
    have he i (hi:i≤N) : |β i-Camp.slope a! cN i| ≤|b| + ∑ j∈Finset.range i,worth a! (j+1):=by
       induction i with
       | zero=> simp only [Camp.first,hr,add_sub_cancel_left,Finset.range_zero,Finset.sum_empty,add_zero,le_rfl]
       | succ i ih=>
          let J:= H.charts i hi; let v:= Tour.bonus R J _ (hs.alive _ hi); have he := (doors H hs i hi).1
          have he' : (β (i+1)-Camp.slope a! cN (i+1))=(β i -Camp.slope a! cN i)-v:=by change β i=β (i+1)+_+v at he; linarith only [he,Camp.plus (α:=cN) a! i]
          rw [he',Finset.sum_range_succ, ← add_assoc,sub_eq_add_neg]; refine (abs_add_le ..).trans (add_le_add (ih (Nat.le_of_succ_le hi)) ?_); rw [abs_neg]; exact (plates u h H hs hb hr i (Nat.le_of_succ_le hi)).2 hi
    apply mem_closedBall_zero_iff.mpr; refine (pi_norm_le_iff_of_nonneg (by norm_num [rad,rim])).2 (fun i=>?_); unfold port cut; rw [Complex.norm_real,Real.norm_eq_abs,abs_div,abs_of_pos (pulse_pos ..)]; apply (div_le_iff₀ (pulse_pos ..)).mpr
    apply (he _ (Nat.le_of_lt_succ i.isLt)).trans; apply le_trans (add_le_add_right (levy _ hG hf i.val) _)
    have hx: |b|≤ flatTime a!:= (Complex.norm_real b|>.symm.trans_lt (mem_ball_zero_iff.mp hb)).le
    unfold rad flatTime Camp.soft rim at *; linarith only [hx,pulse_mono a! hG (Nat.zero_le i.val),pulse_pos a! i.val]
end Fitted
end YM.UVExtension.Spire
