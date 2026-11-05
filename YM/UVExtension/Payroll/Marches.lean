import YM.UVExtension.Concert.Hearth
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Payroll
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open ConnectedActivityE6
open Packets PhysicalNext PhysicalNext.Repeat Marlin Meadow Animals Slide Song Trio Wick Lamppost
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Progress.DirectedRecipe
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical
-- Block budgets on wider courtyard PRIOR to cancellations
variable {G : Gauge} {S:Patch}{P:Teller G} {Q : Target G P} {L:Side} {U W μ β ξ:ℝ} {o : Target.Order G W} {C: RG.Stage}
-- monitor funds use gap squared but park appeals much later
def prize (G : Gauge)(L:Side)(x:ℝ)(ε:ℝ):ℝ:= ε * ConnectedActivityE6.incomingK G L x
def pay (G:Gauge)(L:Side)(x:ℝ):= betaF G x L ^ (-(1/8:ℝ))
lemma cashiers (L:Side) {ε:ℝ}(he:0<ε) : ∀ᶠ x in atTop,∀ (a b:ℝ),0≤a→0≤b→ a≤prize G L x ε/8 → b ≤ pay G L x → ∃ κ, Payments.Rates (radiusB x) (prize G L x ε) a b κ:= by
  let Z x:= prize G L x ε; let P x:=(betaF G x L)^((1:ℝ)/16); let z:= pay G L; let B:=radiusB
  have hj : Rate G L (-(1/8)) z:= Rate.power; have hP:Rate G L ((1:ℝ)/16) P:= Rate.power
  have h' : Rate G L (-1) Z := (incomingK_rate G L (-1)).mul_left _
  have hp : Rate G L (-(1/16)) (fun x=> (P x)⁻¹):= by apply Rate.congr Rate.power; filter_upwards [Delay.shift_pos G L] with x hx; exact (Real.rpow_neg hx.le _).symm
  have hv : Rate G L 0 (fun x=> ((B x+B x+1:ℕ):ℝ)^4):= by simp only [Nat.cast_add,Nat.cast_one]; simpa only [zero_mul] using! (((Rate.radius_price (G:=G) (L:=L)).add Rate.radius_price).add (Rate.const 1)).pow 4
  filter_upwards [hj.below (by norm_num) 1 zero_lt_one,(h'.mul hP).below (by norm_num) 1 zero_lt_one, Delay.shift_pos G L,(hv.mul ((hp.mul_left (1/8)).add ((hj.mul_left 2).weaken (by norm_num)))).below (by norm_num) 1 zero_lt_one,(hP.mul hj).below (by norm_num) (1/8) (by norm_num)] with x he' hy hz hK hv a b u hh hx hr
  have hg :0 < Z x:=mul_pos he (Real.exp_pos _); have hY:0< P x:= by unfold P; positivity
  refine Marlin.pennies hg hY u hh hx ((le_abs_self _).trans hy) (hr.trans ((le_abs_self _).trans he')) ?_ ((mul_le_mul_of_nonneg_left hr hY.le).trans ((le_abs_self _).trans hv))
  exact (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ)≤2))) (show 0≤ ((B x+B x+1:ℕ):ℝ)^4 by positivity)).trans ((le_abs_self _).trans hK)
lemma stipend (L:Side) : ∀ᶠ x in atTop, ConnectedActivityE6.incomingK G L x ≤ Real.exp (-((Vac.Numbers.P x)^((1:ℝ)/5))) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.comp Real.tendsto_log_atTop|>.eventually_ge_atTop 1] with x hx h
  apply Real.exp_le_exp.mpr; apply neg_le_neg; apply Real.rpow_le_rpow (Real.exp_pos _).le _ (by norm_num)
  unfold Delay.fineMonitor Vac.Numbers.P
  apply Real.exp_monotone; apply pow_le_pow_left₀ (zero_le_one.trans h); apply Real.log_le_log (Real.log_pos hx)
  exact Real.log_le_log (zero_lt_one.trans hx) (le_add_of_nonneg_right (Work.E04.shift_nonneg G L))
lemma soaredK (Q:Target G P) (L:Side)(hm:0<μ) (he:0<ξ) : ∀ᶠ x in atTop, 0 ≤ Cash.armK Q L μ x 0 0 ∧ Cash.armK Q L μ x 0 0 ≤ prize G L x ξ/8:=by
  have hx := (Q.tempo L hm 0).below Q.stop (ξ/16) (by positivity)
  -- use that p→∞
  have he' : Tendsto (Delay.fineMonitor G L) atTop atTop:= by
    have h:= Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)); exact Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (n:=2) (by norm_num)).comp h)
  filter_upwards [he'.eventually_ge_atTop (4/μ),he'.eventually_ge_atTop (1:ℝ),Delay.shift_pos G L,hx] with x hh hp ht hv
  let m:=Delay.fineMonitor G L x
  have h: m^((1:ℝ)/5)≤Q.mark L μ x:= calc
    _ ≤ m:= by simpa using (Real.rpow_le_rpow_of_exponent_le hp (by norm_num : (1:ℝ)/5 ≤1))
    _ ≤ μ/4*m^2:= by change 1 ≤ m at hp; change 4/μ ≤ m at hh; have hh':= (div_le_iff₀ hm).mp hh; nlinarith
    _ = _:= by change _= μ/2*(1/2)*m^2; ring
  let V:=Q.overture L μ x 0; let Z:=Q.mergeScale L μ x 0; have hY:0<Z:=mul_pos (by norm_num) (Q.overture_pos x 0 ht)
  have hx:Z*(1-1/2)⁻¹≤ξ/8:= by norm_num; linarith only [show Z≤ξ/16 from (le_abs_self _).trans hv]
  unfold Cash.armK; rw [pow_zero,inv_one,one_mul]; refine ⟨mul_nonneg (Real.exp_pos _).le (show 0≤Z*(1-1/2)⁻¹ by positivity),?_⟩
  let b:= Real.exp (-Q.mark L μ x); let f:= ConnectedActivityE6.incomingK G L x
  have hf : b≤f:=Real.exp_monotone (neg_le_neg h)
  exact (mul_le_mul_of_nonneg_left hx (Real.exp_nonneg _)).trans ((mul_le_mul_of_nonneg_right hf (by positivity:0≤ξ/8)).trans_eq (by unfold prize; ring))

-- t used for E visitation after preliminary E estimate is exposed as pow(t)
variable (G : Gauge)(L:Side)(C: RG.Stage)(b:ℕ)
def drum (x:ℝ):=4*Height.away C*(betaF G x L ^ (-(1/3:ℝ))+4*(betaF G x L ^ (-(7/16:ℝ))))
def clang (x:ℝ):= (ballCost (Meadow.studio b (radiusB x)):ℝ)*drum G L C x
lemma high : Rate G L (-(1/3)) (drum G L C):= (Rate.power.add ((Rate.power.mul_left 4).weaken (by norm_num))).mul_left _
lemma sharp : Rate G L (-(1/3)) (clang G L C b):=by simpa only [zero_add] using! (Trio.balls G L (Trio.rows G L b|>.1)).mul (high G L C)
def whale (x : ℝ):= Concert.arenaE (Time.probe C) (Trio.base b (radiusB x)) (Trio.fence b (radiusB x)) (fun _=> clang G L C b x)
def whaleK (x:ℝ):= Concert.arenaK (Trio.fence b (radiusB x)) (fun _=> clang G L C b x)
lemma panels (x:ℝ)(p:BudgetPoint)(h:Time.Same C p) : turnFee p=Height.away C∧ preExponent p=preExponent (Time.probe C)∧p.supportExponent=(Time.probe C).supportExponent∧ Concert.arenaE p (Trio.base b (radiusB x)) (Trio.fence b (radiusB x)) (fun _=>clang G L C b x)=whale G L C b x:= by
  refine ⟨?_,?_, h.2.2,?_⟩
  · unfold turnFee Height.away; rw [h.2.1,h.1]
  · unfold preExponent; rw [h.2.2]; rfl
  unfold whale Concert.arenaE Trio.tilt; simp_rw [h.2.1,h.1]; rfl
lemma marlin_rate : Rate G L (-(1/3)) (whale G L C b) ∧ Rate G L (-(1/3)) (whaleK G L C b):= by
  have hv:= sharp G L C b
  have hx:= (Trio.rows G L b).2.2.1
  let g x:= Trio.tilt (Time.probe C) (Trio.base b (radiusB x)); have hg:Rate G L 0 g:=
    ((Lantern.Bolt.still _).times (((Lantern.Bolt.still 1).joins hx).nod ((Time.probe C).power*(Time.probe C).order))).uses
  constructor
  · refine Trio.sparks G L (f:=fun i x=> |Slide.ray i| * ((Fintype.card (Site (Trio.fence b (radiusB x) i)):ℝ)*(2*g x*(clang G L C b x+clang G L C b x)))) (fun i=>?_) 
    simpa only [zero_add] using! (((Trio.feeStars G L b i).mul ((hg.mul_left 2).mul (hv.add hv))).mul_left |ray i|)
  refine Trio.sparks G L (f:=fun i x=> |Slide.ray i| * ((Fintype.card (Site (Trio.fence b (radiusB x) i)):ℝ)*(clang G L C b x+clang G L C b x))) (fun i=>?_)
  simpa only [zero_add] using! (((Trio.feeStars G L b i).mul (hv.add hv)).mul_left |ray i|)
def seek (x:ℝ):= drum G L C x +4*Height.away C*(Real.exp (preExponent (Time.probe C)*Trio.coverTicket b)* whale G L C b x)
def freshW (x:ℝ):= Marlin.tithe (2*Trio.base b (radiusB x)) (clang G L C b x+clang G L C b x+whaleK G L C b x) (Time.probe C) (Trio.coverTicket b)
lemma harvest: Rate G L (-(1/3)) (seek G L C b) ∧ Rate G L (-(1/3)) (freshW G L C b):= by
  have he:=marlin_rate G L C b; have hv:= sharp G L C b
  refine ⟨(high G L C).add ((he.1.mul_left _).mul_left _),?_⟩
  simpa only [zero_add] using! (((Trio.balls G L ((Trio.rows G L b).2.2.2)).mul ((hv.add hv).add he.2)).mul_right (Real.exp ((C.supportExponent+1+1)*coverTicket b)))
end YM.UVExtension.Payroll
