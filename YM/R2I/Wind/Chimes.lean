import YM.R2I.Wind.Ports
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Tables
import YM.R2I.Vale.Shed
/-!
# uniform every-history winding correction receipts
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset.Averaging.Wind
open Function Filter Set Lattice Wilson RG StressFlux Finset
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical
open Ovens Ovens.Pipes Progress.DirectedRecipe Collection Quotes Time
open Precision Pressure PhysicalNext.Repeat Lease Next.Scheduling RG.Supply Push.AbsoluteSums Extra.Iteration
open WilsonStartup Payments Footprint Geo UVNext.PricedKernels ConnectedActivityE6
variable (G:Gauge){P:BudgetPoint}{n:Side}(T:Stage)
def coin (P:BudgetPoint)(n:Side):= chunk P n 2
def both (G:Gauge)(P:BudgetPoint)(n:Side):=spendX ((1+turnFee P)*lilac G P (coin P n)) P n
lemma combineCharge {G:Gauge}{q P':ℝ}(h : |q| *P.threshold^2 ≤ P' * coin P n) :
       spendX (turnFee P*lilac G P (|q| *P.threshold^2)) P n ≤ P' * both G P n ∧ spendX (lilac G P (|q| *P.threshold^2)) P n ≤ P'*both G P n:= by
   let s:= lilac G P (|q| *P.threshold^2); have hp : 0≤ s:= by unfold s lilac; have h:=tollG_nonneg (G:=G) (P:=P); positivity
   have he:= (mul_le_mul_of_nonneg_right h (tollG_nonneg (G:=G) (P:=P))); have hx: 0≤ turnFee P:= (turnFee_pos P).le
   let T (x:ℝ):= spendX x P n; have ht:Monotone T:= by intro a b hab; unfold T spendX; gcongr
   have hh : T ((1+turnFee P)*s) ≤ P'*both G P n:= by
     apply le_trans (ht (mul_le_mul_of_nonneg_left he (add_nonneg zero_le_one hx))); apply le_of_eq; unfold T both spendX lilac; ring
   exact ⟨(ht (show turnFee P*s ≤ (1+turnFee P)*s by linarith only [hp])).trans hh,(ht (le_mul_of_one_le_left hp (by linarith))).trans hh⟩
variable (t:ℝ)
-- post comparison quote relative to H*share
structure Purchase (G:Gauge) (P:BudgetPoint)(n:Side) (y:ℝ) (j:ℕ) : Prop where
    rebate : both G P n ≤ resetFee G P /4
    vote : both G P n ≤ softReset G P 1/4
    scale : coin P n ≤ y ^ (- (j:ℝ))
    renew : both G P n ≤ y ^ (-(j:ℝ))
-- quote trigger. not budgeting costs assumed in *base* sale.
set_option quotPrecheck false
local notation "a"=> (n.val:ℝ)
section support
variable {r:ℕ} (hn:200*(1+r)^2≤n.val)
local notation "k" => brake r n
include hn
private lemma atopP: 20 < n.val ∧ r ≤ k ∧ n.val ≤ 100*(1+k)^2:=by
   have he:20<n.val:=by nlinarith [Nat.zero_le r, Nat.zero_le (r^2)]
   have h:= toll he r; have hh:r ≤ k:=by by_contra! hu; nlinarith -- mult
   exact ⟨he,hh,by nlinarith⟩
lemma ceilings (d:ℕ) : (n.val:ℝ)^d * Real.exp (-2*(k:ℝ)) ≤ (100^d*(2*d).factorial*Real.exp 1) * Real.exp (-(r:ℝ)) := by
   obtain ⟨ht,hq,h⟩:= atopP hn; let p:ℝ:=k; have hv:0≤p:= Nat.cast_nonneg _; have he:0<a:=Nat.cast_pos.mpr n.pos
   let f:ℝ:= (2*d).factorial; have hF:0≤f:=Nat.cast_nonneg _
   calc
     _ ≤ (100*(1+p)^2)^d *Real.exp (-2*p):= by
       apply mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he.le ?_ _) (Real.exp_pos _).le; unfold p; exact_mod_cast h -- need unfold p
     _ =100^d*(1+p)^(2*d)*Real.exp (-2*p):=by rw [mul_pow,← pow_mul]
     _ ≤100^d*(f * Real.exp 1 * Real.exp p)*Real.exp (-2*p):= by
       gcongr; exact (polynomial_cost zero_lt_one hv (2*d)).trans_eq (by simp [f])
     _ = (100^d*f*Real.exp 1)*Real.exp (-p):=by rw [mul_assoc _ (_*Real.exp p) _, mul_assoc (f*Real.exp 1),← Real.exp_add,show p+ -2*p=-p by ring]; ring
     _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_monotone (by change -p ≤ - (r:ℝ); gcongr; unfold p; exact_mod_cast hq)) (show 0≤(100^d*f*Real.exp 1) by positivity)
end support
section lease
variable (hp : Same T P)
variable (hn : 200*(1+P.B)^2 ≤ n.val)
def pace (d:ℕ) := (100:ℝ)^d*(2*d).factorial * Real.exp 1
def bloom (P:BudgetPoint) := (Fintype.card Signed:ℝ)*12*Real.exp ((P.supportExponent+1)*81)*((1+turnFee P)*tollG G P)
lemma soft_credit {H:ℝ} : H*softReset G P 1/4=softReset G P (H/4):= by unfold softReset Footprint.payment degreeIncome; ring
lemma turn_same : 0 ≤ bloom G P := by unfold bloom; have h:=tollG_nonneg (G:=G) (P:=P); have h:=turnFee_pos P; positivity
include hp
lemma flower : bloom G P = bloom G (Time.probe T):= by unfold bloom turnFee Lease.tollG pairBill Time.probe; dsimp only; simp only [hp.1,hp.2.1,hp.2.2]
include hn
lemma vote : both G P n ≤ bloom G (Time.probe T)*pace 14*Real.exp (-(P.B:ℝ)):=by
   let p:ℝ:=brake P.B n
   rw [← flower G T hp]; have h:= ceilings hn 14; unfold both spendX lilac coin chunk roomPrice
   calc
     _ = bloom G P * (a^14*Real.exp (-2*p)):= by
       unfold Seat; rw [Fintype.card_prod,site_card]; push_cast; unfold airGap bloom preExponent
       have he:Real.exp ((P.supportExponent+1)*(p+81))*Real.exp (-((P.supportExponent+3)*p))=Real.exp ((P.supportExponent+1)*81)*Real.exp (-2*p):= by rw [←Real.exp_add,←Real.exp_add]; ring_nf
       dsimp [p] at he ⊢; linear_combination (Fintype.card Signed:ℝ) * 12*a^14*((1+turnFee P)*tollG G P) * he
     _ ≤ _ := (mul_le_mul_of_nonneg_left h (turn_same G)).trans_eq (by unfold pace; ring)
omit hp
lemma renews : coin P n ≤ (12*pace 10) * Real.exp (-(P.B:ℝ)):= by
   let p:ℝ:=brake P.B n; have h:= ceilings hn 10; have hk:0≤p:=Nat.cast_nonneg _
   have ht : airGap P n ≤ Real.exp (-2*p):= Real.exp_monotone (by unfold preExponent; unfold p at *; nlinarith only [P.exponent_pos,hk])
   refine (mul_le_mul_of_nonneg_left ht (show 0≤roomPrice n 2 from by unfold roomPrice; positivity)).trans (?_)
   unfold p roomPrice pace; linarith only [h]
omit hn
include hp
lemma soft_base : softReset G (Time.probe T) 1 ≤ softReset G P 1:= by
    have he:Residual.resetLoss G (Time.probe T)=Residual.resetLoss G P:= by unfold Residual.resetLoss Residual.multiplier pairBill Time.probe; dsimp; rw [hp.1,hp.2.1]
    have hh: (Time.probe T).supportExponent=P.supportExponent:= hp.2.2.symm
    have hz : 0≤(1 - Real.exp (-(1:ℝ)))⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))
    have hP:0 ≤Residual.resetLoss G P:= (Residual.loss_pos ..).le
    unfold softReset Footprint.payment degreeIncome Footprint.spread Animals.ballCost; rw [he,hh]; dsimp only [Time.probe]; have hu:=P.B_pos; push_cast; gcongr; exact_mod_cast (show 28561 ≤ 1 * (4 * P.B + 2 + (4 * P.B + 2) + 1)^4 from by rw [one_mul,show (28561:ℕ) = 13^4 by norm_num]; gcongr; omega)
lemma regular_base : resetFee G P=resetFee G (Time.probe T):= by unfold resetFee Residual.resetLoss Residual.multiplier pairBill Time.probe; dsimp; rw [hp.2.2,hp.1,hp.2.1]
omit hp
lemma buys (L:Side)(j:ℕ): ∀ᶠ s : ℝ in atTop, ∀ P : BudgetPoint, P.B=radiusB s → ∀ n:Side, 200*(1+P.B)^2≤n.val→ Time.Same T P → Purchase G P n (betaF G s L) j:= by
    let v:ℝ:=-(j:ℝ); let W t:= Real.exp (-(radiusB t:ℝ))
    have hf : ConnectedActivityE6.Rate G L (v-1) W:= by
      apply Rate.compare (Rate.cutoff zero_lt_one); filter_upwards with t; rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]; apply Real.exp_monotone; rw [neg_mul, one_mul]; exact neg_le_neg (show ((Pressure.Stores.till t):ℝ) ≤ radiusB t from by exact_mod_cast Nat.div_le_self ..)
    let p:=Time.probe T; have ht:=T.price_pos
    let T':= resetFee G p; let J:= softReset G p 1
    have hv:0<T':= mul_pos (Real.exp_pos _) (Residual.loss_pos ..)
    have hx:0<J:=by
      have he:0< 1 - Real.exp (-(1:ℝ)) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)); have hh:0<Residual.resetLoss G p:= Residual.loss_pos ..; unfold J softReset Footprint.payment degreeIncome Footprint.spread Animals.ballCost; positivity
    let C:=bloom G p*pace 14; have hh:= hf.mul_left C; have hb:v-1<0:= by unfold v; linarith [Nat.cast_nonneg (α:=ℝ) j ]
    have h:v-1<v:=by linarith
    filter_upwards [hh _ h, hh.below hb (T'/4) (by positivity), hh.below hb (J/4) (by positivity), hf.mul_left (12*pace 10) _ h] with s h hT hL hU P hP n hn hpe
    have hz:both G P n≤ C*W s:= (vote G T hpe hn).trans_eq (by unfold W; rw [← hP])
    have hi:= soft_base G T hpe; have hH:T'=resetFee G P:=(regular_base G T hpe).symm; rw [hH] at hT
    refine ⟨hz.trans ((le_abs_self _).trans hT),hz.trans ((le_abs_self _).trans (hL.trans ?_)), ?_,hz.trans ((le_abs_self _).trans h)⟩
    · exact div_le_div_of_nonneg_right hi (by norm_num)
    apply (renews hn).trans; rw [hP]; exact (le_abs_self _).trans hU
end lease
end YM.AnalyticBridge.VerifiedReset.Averaging.Wind
namespace YM.PhysicalNext.Repeat.Roof
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {M:Metals G} {p:Sheet G} (D:Rolls p){q:Protection D} (T:Delays q)
open Averaging
structure WindFare : Prop where
   shelter j : 200 ≤ T.shells j ∧ 2 ≤ T.growth j
   credit j i: StepStages j i → ∀ t:ℝ, T.betaEntry j≤t → ∀ P:BudgetPoint,P.B=radiusB t→∀ n:Side,200*(1+P.B)^2≤ n.val → Time.Same (p.profile i) P → Wind.Purchase G P n (betaF G t (D.L j)) j
lemma windTime : ∃ U:Delays q,DelayLe T U ∧ ∀ V:Delays q,DelayLe U V→ Roof.WindFare D V:= by
   obtain ⟨x,-,hp,hv⟩:=collect_upper T.betaEntry _ fun j=>eventually_transitions j _ _ fun i (_he:StepStages j i)=> Wind.buys G (p.profile i) (D.L j) j
   refine ⟨{T with betaEntry:=x, shells:=fun i=> T.shells i+200, growth:=fun i=> T.growth i+2},⟨hp,le_rfl,fun _=> Nat.le_add_right ..,fun _=> Nat.le_add_right ..⟩,fun V h=>⟨fun i=> ?_, fun i j hi t ht=>?_⟩⟩
   · exact ⟨(Nat.le_add_left 200 _).trans (h.shells i),(Nat.le_add_left 2 _).trans (h.growth i)⟩
   exact hv _ _ ((h.beta _).trans ht) j hi
variable {D:Rolls M.p}(A:Alloy M D) (ht:WindFare D A.delay)
include ht
set_option quotPrecheck false
local notation "P" => A.B.a.budget
lemma payments (j i:ℕ) : Wind.Purchase G (P j) (A.B.a.S.side j i) (A.B.a.clock.hatBeta (j+1)) (A.B.a.clock.J (j+1)) := by
   let L := D.L (A.B.a.clock.J (j+1))
   have hv := ht.shelter (A.B.a.clock.J (j+1)); have hg := A.B.valid.volume j i
   rw [PriceCompiler.beta_eq A.B.valid]
   refine ht.credit _ _ (step_paid A.B.a j) _ (A.B.valid.pays _) _ rfl _ ?_ ?_
   · let b:= (P j).B; let k:= A.B.a.clock.coverSize (j+1); let η:= A.B.a.clock.J (j+1)
     refine le_trans (?_) hg; change 200*(1+b)^2 ≤ A.delay.shells η *(1+b+k)^ (A.delay.growth η)
     refine Nat.mul_le_mul hv.1 ((show (1+b)^2≤(1+b+k)^2 from Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by omega) hv.2))
   obtain ⟨h1,h2,h3,-⟩:= Rain.jersey (A:=A) (m:=j); exact ⟨h2,h1,h3⟩
end YM.PhysicalNext.Repeat.Roof
#print axioms YM.PhysicalNext.Repeat.Roof.windTime
