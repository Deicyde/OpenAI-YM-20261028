import YM.RemainderComparison.Lyric.Flux

/-! # Sufficient stage price for active marked tails
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lyric
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Next.Scheduling
open Merge Palette
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L':ℝ}{j n:ℕ}(χ:Chi)

open Daisy
local notation "X'" => Palette.mark M (c:=c)
local notation "Lk" => ConnectedActivityE6.lengths T R
local notation "sx" => radiusB x
variable (l:ι→ℝ) (N:Captain H j q d v u A b r B e n χ)
open Height AnalyticBridge.VerifiedReset
variable {δ Gp:ℝ}
open Delay

def ink (Q:ConnectedActivityE6.Target G P) (L:Side)(x:ℝ)(m:ℕ)(p:ℝ):= m * Extra.Multi.siteFactor (radiusB x) * (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5)) * ((grow G L x*(tax G L x)⁻¹)*p))
section
lemma tax_inverse (G:Gauge)(L:Side)(m:ℕ): Rate G L (-(3/8:ℝ)*m) (fun x=> ((grow G L x)^m)⁻¹):=by
   apply Rate.power.congr; filter_upwards [Delay.shift_pos G L] with x hx
   unfold Height.grow; rw [← Real.rpow_mul_natCast hx.le,neg_mul,Real.rpow_neg hx.le]
lemma ink_cost (Q:ConnectedActivityE6.Target G P) (L:Side) {m:ℝ→ℕ} {pB:ℝ→ℝ}
    (hm:Rate G L 0 (fun x=>(m x:ℝ)))(hp:Rate G L 0 pB) : Rate G L (-3/2) (fun x=>ink Q L x (m x) (pB x)):=by
   have hG := tax_inverse G L 5
   have ht:= (Rate.power (G:=G) (L:=L) (a:=3/8)).mul hG; have hb:= Rate.radius_price (G:=G) (L:=L)
   have hh: Rate G L 0 (fun x=> Extra.Multi.siteFactor (radiusB x)):=by
     simpa only [Extra.Multi.siteFactor,zero_mul] using! ((((((hb.mul_left 16).add (Rate.const 9)).mul_left 2).pow 4).mul_left (Real.exp 1)))
   convert! ((hm.mul hh).mul ((ht.mul hp).mul_left (Real.exp ((Q.relative+1)*Footprint.preCost (Q.halo+5))))) using 1; norm_num

lemma mark_force (Q:ConnectedActivityE6.Target G P)(L:Side) (h:0<μ) (a b:ℝ) (hb:0<b): Rate G L a (fun x=> Real.exp ((-Q.mark L μ x)*b)):=by
   apply (Rate.monitor_cutoff (show 0< μ/4*b by positivity) (show (0:ℝ)<2 by norm_num)).congr
   apply Eventually.of_forall; intro i; apply congrArg Real.exp; rw [Real.rpow_two]
   unfold Target.mark Target.costs Push.AbsoluteSums.Buy.quote Delay.hatWin; ring
/-- denominator in local contract (at coarse clock hat beta, define also
 strong retained unit). -/
def unitK (x:ℝ):= Real.exp (-(Vac.Numbers.P x)^((1:ℝ)/5))
lemma strongK (Q:ConnectedActivityE6.Target G P)(L:Side)(hp:0<μ):
     ∀ᶠ x in atTop, Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) ≤ (unitK x)^4 := by
   let A:ℝ:=4
   have hf:= Delay.wins G L (half_pos hp) (show (0:ℝ)<1/2 by norm_num) (show 0≤A by unfold A; positivity) (show (1/5:ℝ)<2 by norm_num) 0
   filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.comp Real.tendsto_log_atTop |>.eventually_ge_atTop 1,hf] with x hx h ht
   have ht': Vac.Numbers.P x ≤ Delay.fineMonitor G L x := by
     unfold Delay.fineMonitor Vac.Numbers.P
     have hh:0<Real.log x:=Real.log_pos hx
     apply Real.exp_monotone; apply pow_le_pow_left₀ (zero_le_one.trans h); apply Real.log_le_log hh
     apply Real.log_le_log (zero_lt_one.trans hx) (le_add_of_nonneg_right (Work.E04.shift_nonneg G L))
   rw [pow_zero,mul_one] at ht
   unfold unitK; rw [← Real.exp_nat_mul]; apply Real.exp_monotone
   let M:= Q.mark L μ x; have hh: 0 < M:= Delay.win_pos G L x (half_pos hp) (show (0:ℝ)<1/2 by norm_num)
   have hy:= Real.rpow_le_rpow (show 0≤Vac.Numbers.P x from (Real.exp_pos _).le) ht' (show (0:ℝ)≤1/5 by norm_num)
   change 4*_≤M/16 at ht; change -M*(1/2:ℝ) ≤ _; push_cast; linarith
lemma tailO (Q:ConnectedActivityE6.Target G P)(L:Side) (hR:0<μ)(k:ℕ):
     ∀ᶠ x in atTop, grow G L x^k ≤ Real.exp (Q.mark L μ x) ∧ grow G L x^k ≤ Real.exp (Q.ε*Pressure.Stores.till x) := by
  have hp:= (Rate.power (G:=G) (L:=L) (a:=3/8)).pow k
  let u:ℝ:= -1-3/8*k
  have hv := mark_force Q L hR u 1 zero_lt_one; simp_rw [mul_one] at hv
  have he:3/8*(k:ℝ)+u < 0:=by unfold u; linarith
  filter_upwards [(hp.mul hv).below he 1 zero_lt_one, (hp.mul (Rate.cutoff Q.usable)).below he 1 zero_lt_one] with x hx hM
  have h (t:ℝ) (hz: |grow G L x^k*Real.exp (-t)| ≤ 1): grow G L x^k ≤ Real.exp t:=(div_le_one (Real.exp_pos _)).1 ((le_abs_self _).trans (by simpa only [div_eq_mul_inv,Real.exp_neg] using! hz))
  exact ⟨h _ hx,h _ (by simpa only [neg_mul,Height.grow] using hM)⟩
end

-- high threshold adjustable. supply via each Wish.
def region (q s:ℕ):ℕ:= 5*q+2*s

structure Premium (Q:ConnectedActivityE6.Target G P)(L:Side) (x a μ b B:ℝ)(j n k s J m:ℕ)(p:ℝ) : Prop where
   visit : Bikes Q L μ x a b B j n
   weight : ink Q L x m p ≤ Daisy.ribbon Q L x
   roll : 1 ≤ grow G L x
   pace : degreePrice (radiusB x) (grow G L x*((Q.costs L μ 1 x 0).rootHit+ink Q L x m p)) Q.δ ≤ 1/2
   stamp : degreePrice (radiusB x) (salaries Q L μ x B (ink Q L x m p) j n) b ≤ 1/2
   retain : grow G L x^region k s ≤ Real.exp (Q.mark L μ x) ∧ grow G L x^region k s ≤ Real.exp (Q.ε*Pressure.Stores.till x)
   bounty : ∀ β, inBand (betaF G x L) β→ ((tax G L x)^k) * (((grow G L x)^region k s)⁻¹*(collars G b x j J*(salaries Q L μ x B (ink Q L x m p) j n*(1-1/2)⁻¹))) ≤ (gStep β)^s
   inkForce : ∀ β, inBand (betaF G x L) β → tax G L x^k*(Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n))≤ Real.exp ((-Q.mark L μ x)*(1/2:ℝ)) * (gStep β)^s -- stronger than divisor and avoids relying on input mass positivity
   trained : Real.exp ((-Q.mark L μ x)*(1/2:ℝ))≤ unitK x^4

lemma Premium.forced {L:Side}{n k s J m:ℕ}{x a μ b B p:ℝ} (h: Premium Q L x a μ b B j n k s J m p) (β:ℝ)(hp:inBand (betaF G x L) β) : tax G L x^k*(Real.exp (-Q.mark L μ x)*(2*Daisy.pledgeQ L Q μ x B j n)) ≤ unitK x^4 * (gStep β)^s:= (h.inkForce β hp).trans (mul_le_mul_of_nonneg_right h.trained (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _))

lemma epochs (Q:ConnectedActivityE6.Target G P)(L:Side) (hp:3/8+Q.rate<0)(ha:0≤ a)(hd:0<δ)(hv:a+δ+δ≤ Q.exp)(hμ:0<μ)
    (j n k s J:ℕ) {B p:ℝ→ℝ}{m:ℝ→ℕ}(hB:Rate G L 0 B)(hp':Rate G L 0 p)(h':Rate G L 0 (fun i=> (m i:ℝ))) : ∀ᶠ x in atTop,
       Premium Q L x a μ δ (B x) j n k s J (m x) (p x) := by
   have hS:= ink_cost Q L h' hp'; let X x:= ink Q L x (m x) (p x)
   let u:= 3/8+Q.rate; have hu:u<0:=hp
   have ht := (Q.rate_root L hμ (C:=0) (β:=1)).add (hS.weaken (by linarith only [Q.start]))
   let p' x:= salaries Q L μ x (B x) (X x) j n
   have he : Rate G L u p':=by
      let b:ℝ:= 2^j
      have hA := ((Rate.power (G:=G) (L:=L) (a:=3/8)).mul ht).mul_right ((1- (1:ℝ)/2)⁻¹)
      unfold p' salaries treeYield; simp_rw [pow_zero,mul_one]; simpa only [zero_add] using! (((Rate.const 1).add (hB.mul_left b)).mul (hA.mul_left (polyPrice Q.ε n)))
   have hr R (h:Rate G L u R): Rate G L u (fun x=> degreePrice (radiusB x) (R x) δ):=by
      unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]; have he:= Census.width_rate G L 1 0; simp only [one_mul,add_zero] at he; simpa only [zero_add] using! (((he.mul h).mul_right δ⁻¹).mul_left 4)
   have hz := Daisy.stables L Q hμ B hd hv ha hB j n J
   have hs := Height.pressureYoung G L (i:=Q.δ) ht hp
   let K:= Real.exp (Q.relative*preCost (Q.halo+5)); have hK:0<K:=Real.exp_pos _
   let c:= region k s; have hy: Rate G L 0 shiftG := (((Rate.radius_price).mul_left 2).add (Rate.const 1)).mul_left 4
   have hh₀:Rate G L 0 (fun x=> collars G δ x j J):= by simpa only [zero_mul] using! ((hy.pow (J*j)).mul_right (polyPrice δ (J*j)))
   let Y:=3/8*(5:ℕ)*(k:ℝ); have hh: Rate G L Y (fun x=> (tax G L x)^k):= ((Rate.power (G:=G) (L:=L) (a:=3/8)).pow 5).pow k
   let t:= -(s:ℝ)/2-1 -Y -Q.rate; let p0 x:=Real.exp ((-Q.mark L μ x)*(1/2:ℝ)); let z x:= 2*Daisy.pledgeQ L Q μ x (B x) j n
   have hE:= (hh.mul ((mark_force Q L hμ t _ (by norm_num:(0:ℝ)<1/2)).mul ((Daisy.scaleHome L Q hμ j n hB).2.mul_left 2)))
   filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,hz, hs,(hr p' he).below hp _ (by norm_num:(0:ℝ)<1/2),tailO Q L hμ c,(hS.mul_right K⁻¹) Q.rate (by linarith only [Q.start]),Access.exchange _ s (by unfold Y c region; push_cast; linarith) (hh.mul ((tax_inverse G L c).mul (hh₀.mul (he.mul_right ((1- (1:ℝ)/2)⁻¹))))), strongK Q L hμ,Access.exchange _ s (by unfold t; linarith only) hE] with x hx hB hS hh hp ht h H hE
   refine ⟨hB.1,?_,Real.one_le_rpow hx (by norm_num), hS, (le_abs_self _).trans hh,hp,fun β hv=> (le_abs_self _).trans (h β hv),fun β hv=>?_,H⟩
   · unfold Daisy.ribbon; apply (div_le_iff₀ hK).1; rw [div_eq_mul_inv]; exact (le_abs_self _).trans ht
   let g:=gStep β; have he:0 ≤ g := inv_nonneg.mpr (Real.sqrt_nonneg _)
   have ht : Real.exp (-Q.mark L μ x)= p0 x * p0 x := by unfold p0; rw [← Real.exp_add]; ring_nf
   change tax G L x^k*(Real.exp _*z x) ≤ p0 x* g^s; rw [ht]
   apply le_trans _ (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hE β hv)) (show 0 ≤ p0 x from (Real.exp_pos _).le)); apply le_of_eq; unfold p0 z; ring
end YM.RemainderComparison.Lyric
