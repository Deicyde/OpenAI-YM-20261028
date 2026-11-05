import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Confetti
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Eco
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roost.Foundry
/-!
 # Prebudget mode for rooted corners. Held-t derivative ledger, K.Stip post priced smaller than license. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Blush
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera Mallow
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity Rain Roost Lotus
open UVNext.CouplingReset Animals Marlin Progress.DirectedRecipe Ovens Ovens.Pipes
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge}
open Next.Foundations Extra.Histories YM.Planned.GuardedAtom
section charges
-- charge arbitrary d.Tau. express.
def glyph (x : ℝ):ℝ:= Real.sqrt (Real.exp (-Real.exp (Real.log (Real.log x)^2) ^((1:ℝ)/5))) -- precedence! neg applies before ^? check.
lemma glyph_eq (a:Levels G)(m : ℕ):Real.sqrt (a.clock.forcedAllowance m)=glyph (a.clock.hatBeta m):=rfl
lemma glyphpos (x:ℝ):0<glyph x:=Real.sqrt_pos.mpr (Real.exp_pos _)
variable {L:Side}{t : ℝ}(ht:0<t)
include ht
lemma efferv (b:ℝ): Rate G L b (fun x=> (glyph x)⁻¹ * straw t L G x):=by
  refine (infuso L 2 (t/4) _ (by positivity) (by norm_num: (0:ℝ)<1/8) b).compare ?_
  have hg:= Delay.monitor_pays G L 0 (hD:=le_of_lt (show (0:ℝ) < 64/t from by positivity)) (show (0:ℝ)<1 by norm_num)
  filter_upwards [eventually_gt_atTop (Real.exp 1), hg] with x hx hh
  let V:= Delay.fineMonitor G L x; let u:=Real.exp ((Real.log (Real.log x))^2)
  have hz : 0≤ Real.log (Real.log x) := Real.log_nonneg ((by rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hx.le)) -- nested rw problem
  have hV : x≤ betaF G x L:=le_add_of_nonneg_right (Work.E04.shift_nonneg ..)
  have hU : u ≤ V:=by
    apply Real.exp_monotone; apply pow_le_pow_left₀ hz _; have he : 1 < x:= lt_trans (Real.one_lt_exp_iff.mpr zero_lt_one) hx; exact Real.log_le_log (Real.log_pos he) (Real.log_le_log (by linarith) hV)
  have hp : 64/t ≤ V :=by simpa using hh
  have hu : u ^ ((1:ℝ)/5) ≤ u := (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) (show (1:ℝ)/5≤1 by norm_num)).trans_eq (Real.rpow_one _)
  unfold straw lauge; rw [abs_of_pos (mul_pos (inv_pos.mpr (glyphpos _)) (mul_pos zero_lt_two (Real.exp_pos _))), abs_of_pos (mul_pos zero_lt_two (Real.exp_pos _)),mul_left_comm]; apply mul_le_mul_of_nonneg_left _ zero_le_two; unfold glyph; rw [Real.sqrt_eq_rpow,← Real.exp_mul, ← Real.exp_neg,← Real.exp_add]; apply Real.exp_le_exp.mpr; change -( -(u^((1:ℝ)/5))*(1/2))+-(t/4)*(1/4)*V^2 ≤ -(t/4)*(1/8)*V^2
  have hT:0<V:=Real.exp_pos _
  have hp':= mul_le_mul_of_nonneg_right ((div_le_iff₀ ht).mp hp) hT.le
  nlinarith

-- knob of fraction y per whole support. Doesn't require ceta Anchor positivity, exactly marker weight cert.
lemma fruition {P:Teller G}(Q:ConnectedActivityE6.Target G P)(A b:ℝ)(hb:0<b):∀ᶠ x in atTop,
    ∀ (c:Side) (R: Rep G c)(S : Cloud R) (o:ℂ),‖o‖ ≤ A →
       let m:=R.p.mass S.live.crest S.live.weight
       let V:= Blush.marvel (Q:=Q) (x:=x) (L:=L) S; let D:= jewelDebt S.live Q L x
       ‖o‖*(V+V)≤b*m∧ (glyph x)⁻¹*(‖o‖*(D+D)*straw t L G x) ≤ b*m:=by
   have hz : Rate G L (Q.rate/4) (poster Q L):= Rate.power
   have he : Rate G L (-Q.rate) (fun x=>(Q.goal L x)⁻¹):=by
     refine Rate.congr Rate.power ((Delay.shift_pos G L).mono fun x hx=>?_); exact (Real.rpow_neg hx.le Q.rate).symm
   have hh:= (he.mul (efferv (G:=G) ht (Q.rate-1))).mul_left (L:=L) (2*A)
   filter_upwards [(hz.mul_left (2*A)).below (by linarith [Q.stop]) _ hb, hh.below (by linarith) _ hb, Delay.shift_pos G L] with x hy hv hx c R S' o ho m V D
   let e:=Real.exp (-Q.ε*coverNumber R.p.B S'.live.crest); let w:=m*e; let g:=Q.goal L x; have hp : e≤1:=Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Q.usable.le) (by positivity)); have hA:0≤A:=(norm_nonneg o).trans ho
   have hf:0≤ m:= (S'.live.profit).trans (R.p.loMass _ _ S'.live.profit); have hg:0<g:= Real.rpow_pos_of_pos hx _; have hF:0≤w:=mul_nonneg hf (Real.exp_pos _).le
   have hh : w≤ m:=mul_le_of_le_one_right hf hp; have hV :0≤V:=mul_nonneg hF (Real.rpow_nonneg hx.le _)
   have hk :0≤D:=div_nonneg hF hg.le
   constructor
   · apply (mul_le_mul_of_nonneg_right ho (add_nonneg hV hV)).trans
     change A*(w*poster Q L x+w*poster Q L x)≤_
     calc
       _=(2*A*poster Q L x)*w:=by ring
       _ ≤ b*m:= mul_le_mul ((le_abs_self _).trans hy) hh hF hb.le
   refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ho (add_nonneg hk hk)) (show 0≤ straw t L G x from mul_nonneg zero_le_two (Real.exp_pos _).le)) (inv_nonneg.mpr (glyphpos _).le)).trans ?_
   change _ * (A*(w/g+w/g)*straw t L G x) ≤ _
   calc
     _ = (2*A*(g⁻¹*((glyph x)⁻¹*straw t L G x)))*w:=by simp_rw [div_eq_mul_inv]; ring
     _ ≤ b*m:= mul_le_mul ((le_abs_self _).trans hv) hh hF hb.le
end charges
end YM.PhysicalNext.Repeat.Blush
