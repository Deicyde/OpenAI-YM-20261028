import YM.FullVolume.Fares.Dusk
/- Acquire tariff & eventual canopy budgets.
 -/
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
open YM.MergeProof MergeProof.Matric FullVolume FullVolume.Paint Tower
open RG.Shoot Lark Motion
open FullVolume FullVolume.Retreat FullVolume.Shroud Amp Amp.Beam
open Pillars Bandage Pass Muse Contest Ovens Veil Ship
variable {R:Run G} {T:Campaign R}
set_option quotPrecheck false
local notation "P"=> R.alloy.B.a
local notation "X"=> R.kit
local notation "D"=> R.rolls
local notation "Φ"=> R.alloy.B.a.clock
open Spirit Branch Boutique Guard
open Extraction Extraction.Lease
open MergeProof.Accent FullVolume.Nectar
variable {I:Type}[Fintype I] [DecidableEq I]
open Face Face.Economics
namespace Sky
variable {Θ:Luna.Tableau T.width 300}{v:ℕ→ℕ→ℝ}(hk:Sky R T Θ v)
local notation "d!"=> intervalClock R
local notation "j!"=> R.alloy.B.a.clock.J
local notation "x!"=> timeEntry R
local notation "C"=>R.alloy.B.a.S
lemma alarm : Tendsto (intervalClock R) atTop atTop:= tendsto_natCast_atTop_atTop.comp (R.alloy.B.a.S.den_strict.tendsto_atTop)
/-- Polynomial budget. No N factors -/
def Timing (θ y:ℕ→ℝ):Prop:= ∀ᶠ b:ℕ in atTop, ∀ᶠ m:ℕ in atTop,|y m|≤ θ m ^ b
namespace Timing
variable {θ f g:ℕ→ℝ}
lemma mk (b:ℕ)(hv:∀ m,1≤ θ m)(h:∀ᶠ m:ℕ in atTop, |f m|≤ θ m ^ b): Timing θ f:=by
    apply (eventually_ge_atTop b).mono; intro k hk; exact h.mono (fun m h=> h.trans (pow_le_pow_right₀ (hv m) hk))
lemma mul (hp:Timing θ f) (hq:Timing θ g)(hv:∀ m,1 ≤ θ m): Timing θ (fun m=> f m*g m):=by
    obtain ⟨b,hb,hv'⟩:= (hp.and hq).exists; refine mk (b+b) hv ?_
    filter_upwards [hb,hv'] with m hm hg; rw [abs_mul,pow_add]; exact mul_le_mul hm hg (abs_nonneg _) (zero_le_one.trans (one_le_pow₀ (hv _)))
lemma pow(hp:Timing θ f)(hv:∀ m,1 ≤ θ m)(d:ℕ):Timing θ (fun m=> f m ^ d):=by
   obtain ⟨b,hb⟩:= hp.exists; apply mk (b*d) hv; filter_upwards [hb] with m hm; rw [abs_pow,pow_mul]; exact pow_le_pow_left₀ (abs_nonneg _) hm _
lemma bound (hp:Timing θ f)(hv:∀ᶠ m:ℕ in atTop,|g m|≤ |f m|):Timing θ g:=hp.mono fun b hb=> hv.mp (hb.mono (fun m hm h=>h.trans hm)) -- order
lemma enlarging{θ':ℕ→ℝ}(hp:Timing θ f)(hv:∀ m,1 ≤ θ m)(h:∀ m,θ m≤ θ' m):Timing θ' f:=hp.mono fun b hb=> hb.mono (fun m hm=> hm.trans (pow_le_pow_left₀ (zero_le_one.trans (hv _)) (h _) _))
lemma static (hv:∀ m,1 ≤ θ m)(hz:Tendsto θ atTop atTop)(x:ℝ):Timing θ fun _=> x:=mk 1 hv (by simpa only [pow_one] using hz.eventually_ge_atTop |x|)
lemma clock (hv:∀ m,1 ≤ θ m): Timing θ θ:= mk 1 hv (Eventually.of_forall fun m=> by rw [pow_one,abs_of_nonneg (zero_le_one.trans (hv m))])
lemma toTick (hp: Timing θ f):∀ᶠ b in atTop,∀ᶠ m in atTop,f m ≤ θ m^b := hp.mono (fun b hb=> hb.mono fun m hm=> (le_abs_self _).trans hm)
end Timing
open Timing
lemma lazy (i:ℕ): intervalClock R i ≤ intervalClock R (i+1):= by unfold intervalClock; exact_mod_cast (R.alloy.B.a.S.den_strict (show i < i+1 from i.lt_succ_self)).le
local notation "V!"=>Timing d!
local notation "W!" => Timing (fun m:ℕ=> intervalClock R (m+1))
lemma Timing.entrenched {x:ℕ→ℝ}(hp:Timing (intervalClock R) x): W! x:= hp.enlarging (fun m=> one_clock _) lazy
lemma mint_eq(m d:ℕ): ‖mintT T d m‖=(intervalClock R m)^d:=by rw [mintT,MergeProof.alto_norm]; unfold Schedule.a; rw [inv_pow,inv_inv]; rfl
lemma stamps (d:ℕ): V! fun m=> ‖mintT T d m‖:=by simp_rw [mint_eq]; exact (clock (fun m=>one_clock m)).pow (fun m=> one_clock m) d
include hk
lemma entry : V! (timeEntry R):=by
   apply Timing.mk 2 (fun m=> one_clock _); let c := G.slopeConstant; let h:ℝ:= (Φ).bar
   have hp : 0≤ c:= (Gauge.slopeConstant_pos T.gains.SimpleR).le
   filter_upwards [(alarm (R:=R)).eventually_ge_atTop (h+c), hk.launches.eventually_ge_atTop 0] with m hm hv
   rw [abs_of_nonneg hv]; let x:= intervalClock R m
   change h + c*(C).scale m ≤ _
   rw [Schedule.scale,Schedule.a,inv_inv]; have hz:1≤x:=one_clock _; have he: Real.log x ≤ x := by linarith only [Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hz)]
   have hθ:0≤ h:= (Φ).bar_pos.le; change h+c*Real.log x≤ x^2; nlinarith only [mul_le_mul_of_nonneg_left he hp,mul_le_mul_of_nonneg_left hz hθ,mul_le_mul_of_nonneg_right hm (zero_le_one.trans hz)]
open Splint
omit hk in
lemma year_era (r:ℕ)(x:ℝ): V! fun m=> x*Real.exp ((C).scale m-(C).scale r):=by
    have hx(m:ℕ): x*Real.exp ((C).scale m-(C).scale r)= (x/Real.exp ((C).scale r))* d! m:=by
       have hb: 0<d! m:=zero_lt_one.trans_le (one_clock _)
       rw [Real.exp_sub]; rw [show Real.exp ((C).scale m)=d! m from (by unfold Schedule.scale Schedule.a; rw [inv_inv]; exact Real.exp_log hb)]; ring
    simp_rw [hx]; exact (Timing.static (fun m=>one_clock m) alarm _).mul (Timing.clock (fun m=>one_clock _)) (fun m=>one_clock m)
omit hk in
lemma Timing.shift (x:ℕ→ℝ)(hp:Timing (intervalClock R) x): W! fun m=> x (m+1):= hp.mono (fun b hb=>by apply (Filter.tendsto_add_atTop_nat 1).eventually (p:=fun m=>|x m|≤ intervalClock R m ^ b) _; exact hb) -- order
lemma cannonE (d:ℕ): Timing (intervalClock R) (fun m=> priceE ((Labels.frames G).level d) (framePay (A:=R.alloy) (m:=m)) (upColumn (R:=R) d m v)):= by
    apply hk.entry.bound
    filter_upwards [(P).fits.deep.eventually_ge_atTop d] with m hm
    apply le_trans _ (le_abs_self _); have hh:= (hk.presents m).framesE d (show d ≤ j! (m+1) from hm.trans ((P).fits.mono (show m≤ m+1 by omega)))
    rw [show (framePay (A:=R.alloy) (m:=m))= Mallow.priceS (G:=G) (R.metals.p.profile (j! (m+1))) from ?_]; exact hh
    unfold framePay Mallow.priceS; rw [show ((P).budget (m+1)).supportExponent=((P).params (m+1)).supportExponent from rfl, params_eq R.alloy.B.valid]
lemma cannonK (d:ℕ):Timing (intervalClock R) (fun m=> priceK Θ.price (R.y ((Φ).J (m+1))) (Doors.rate (R.rolls.L (j! (m+1)))) (R.rolls.L (j! (m+1))) ((Labels.frames G).level d) (upColumn (R:=R) d m v)):= by
    apply hk.entry.bound; filter_upwards [(P).fits.deep.eventually_ge_atTop d] with m hm; exact ((hk.presents m).framesK d (show d ≤ j! (m+1) from hm.trans ((P).fits.mono (by omega)))).trans (le_abs_self _)
lemma topCost(d:ℕ) : V! fun m=> fullCost ((Labels.frames G).level d) ((P).budget m) (Doors.cameras G d):=by
    have hh : V! (fun m => ((P).budget m).threshold⁻¹):=by
       apply hk.entry.bound (Eventually.of_forall fun m=>?_); rw [abs_of_pos (by apply inv_pos.mpr; exact BudgetPoint.threshold_pos _)]
       have he:1 ≤ x! m:= (R.alloy.B.a.fits.delayed m).le; exact (le_trans (b:= x! m) (Doors.temp_cheap he) (le_abs_self _))
    exact (Timing.static (fun m=>one_clock m) alarm _).mul (hh.pow (fun m=>one_clock m) _) (fun m=>one_clock m)
set_option maxRecDepth 8000 in
lemma salaries (d n:ℕ)(z:ℝ) : W! (fun m=>civic n*quoteInput T m v d z) ∧ W! (fun m=> civic n*quoteCert T m Θ v d z) ∧ W! (fun m=> civic n*quoteUnit T m d z) ∧ Timing (intervalClock R) (fun m=> civic n*quoteTop T m d z):=by
    have h(m:ℕ):1≤d! (m+1):= one_clock _; have hv:= year_era (R:=R) (R.t d) z
    have hh:= stamps (T:=T) d; have hg:= Timing.shift _ hh; have hP:= Timing.shift _ hv; have hC (u:ℝ):= Timing.static (fun m=>one_clock (R:=R) m) alarm u; have hx:= (hC (civic n)).entrenched
    refine ⟨hx.mul (((hC 2).entrenched).mul (hg.mul (hP.mul (hk.cannonE d).entrenched h) h) h) h,hx.mul (hh.entrenched.mul (hP.mul (hk.cannonK d).entrenched h) h) h,hx.mul (hg.mul hP h) h,?_⟩
    have hu : Timing (intervalClock R) fun m=> Real.exp (((P).budget m).supportExponent+2):=by
        apply hk.entry.bound; filter_upwards with m; rw [abs_of_pos (Real.exp_pos _),show ((P).budget m).supportExponent=((P).params m).supportExponent from rfl, params_eq R.alloy.B.valid]; exact ((hk.presents m).fame).trans (le_abs_self _)
    let H (m:ℕ) : 1≤ d! m:= one_clock _
    exact (hC _).mul (hh.mul ((hu.mul ((hk.topCost d).mul (hC (χ _)) H) H).mul hv H) H) H -- name conflicts
end Sky
end YM.PhysicalNext.Repeat.Legato.Campaign
#print axioms YM.PhysicalNext.Repeat.Legato.Campaign.Sky.salaries
