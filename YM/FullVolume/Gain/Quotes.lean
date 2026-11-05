import YM.FullVolume.Gain.Resolve
import YM.FullVolume.Cross
/-!
# read Plato from Paid. use native Gap derivatives. Trend fee cumulative purchase via discrete upper vs local salary rise at each step. No tail-sum gate fake contract.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Clock Instrument
variable {G:Gauge}
section rates
variable {q v x y:ℝ}
local notation "ε"=> (31/32:ℝ)
lemma clipS (hp:0<x): Pass.salary x=x^ε:=by unfold Pass.salary Pass.normedWidth; rw [show (31/32:ℝ)=-(1/32)+1 from (by ring),Real.rpow_add hp,Real.rpow_one]
lemma income {a:ℝ}(ha:0<a) :∀ᶠ x in atTop,a*ε*2^(-(1/32):ℝ)*Pass.normedWidth x ≤ Pass.salary (x+a)-Pass.salary x:=by
  let f(x:ℝ):= x^ε; let h(x:ℝ):= ε*x^(ε-1)
  filter_upwards [eventually_ge_atTop a] with x hx; have hp:= ha.trans_le hx; have he:x<x+a:=(by linarith); have hu:=hp.trans he
  obtain ⟨b,hb,hf⟩:= exists_hasDerivAt_eq_slope f h he (by apply Continuous.continuousOn; unfold f; exact continuous_id.rpow_const (fun i=> Or.inr (by norm_num))) (fun i hi=> Real.hasDerivAt_rpow_const (Or.inl (hp.trans hi.1|>.ne')))
  have hb':0<b:=hp.trans hb.1; rw [clipS hu,clipS hp]; rw [show x+a-x=a from by ring] at hf
  apply le_trans _ (le_of_eq ((eq_div_iff ha.ne').mp hf)); unfold h; rw [show ε-1= (-(1/32):ℝ) from (by ring)]
  have hy:= Real.rpow_le_rpow_of_nonpos hb' (show b≤2*x from (by linarith [hb.2])) (show (-(1/32):ℝ)≤0 from (by norm_num))
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hp.le] at hy
  unfold Pass.normedWidth; apply le_trans (b:=(a*ε)*b^(-(1/32):ℝ)) _ (le_of_eq (by ring)); rw [mul_assoc (a*ε)]; exact mul_le_mul_of_nonneg_left hy (by positivity)
lemma hip (h:0<x): gap x=x^(-(1/2):ℝ):= by unfold gap; rw [Real.sqrt_eq_rpow, Real.rpow_neg h.le]
-- t≥gap eventually.Pays. use eventual tilt x carry phi geometry.
lemma trade (G:Gauge)(C:RG.Stage) {a:ℝ}(ha:0<a)(hv:0<v):∀ᶠ x in atTop,2*(chores G C v x/(plain.t x)^2) ≤ glint* (Pass.salary (x+a)-Pass.salary x):=by
  let b:= glint*(a*ε*2^(-(1/32):ℝ)); let c:=2*v*Time.credit G C
  have hb:0<b:= by unfold b glint; positivity
  have hc:0<c:=by unfold c; have hh:=Time.credit_pos G C; positivity
  let t:=(-(1/10):ℝ) - (-(1/32):ℝ)
  have ht:t<0:=by unfold t; norm_num
  have hT := (tendsto_rpow_neg_atTop (show 0< -t from neg_pos.mpr ht)).eventually (gt_mem_nhds (show 0<b/c from div_pos hb hc)); simp_rw [neg_neg] at hT
  filter_upwards [hT,income ha,eventually_gt_atTop (3:ℝ)] with x hx hy hz
  have hp:0<x:= (by linarith); have hfg:=gp hp
  have hq : 1≤plain.P x:=by unfold Instrument.P Clock.watch Instrument.plain; exact Real.one_le_exp (by dsimp; rw [show (2:ℝ)=((2:ℕ):ℝ) from rfl, Real.rpow_natCast]; positivity)
  have hr:0 ≤ 2* chores G C v x:= mul_nonneg (by norm_num) (mul_nonneg hv.le (mul_nonneg (Time.credit_pos ..).le (Real.rpow_nonneg hfg.le _)))
  apply le_trans _ (mul_le_mul_of_nonneg_left hy tintP.1.le)
  rw [← mul_div_assoc]
  apply le_trans (div_le_div_of_nonneg_left hr (pow_pos hfg 2) (show (gap x)^2 ≤ (plain.t x)^2 from pow_le_pow_left₀ hfg.le (le_mul_of_one_le_right hfg.le hq) 2))
  rw [show 2*chores G C v x/(Clock.gap x)^2=c*x^(-(1/10):ℝ) from ?_]; swap
  · unfold chores δE c; rw [hip hp,← Real.rpow_mul hp.le,pow_two,← Real.rpow_add hp, div_eq_iff (Real.rpow_pos_of_pos hp _|>.ne'),mul_assoc ((2:ℝ)*v*Time.credit G C),← Real.rpow_add hp]; norm_num; ring
  change _≤ glint*(_*x^ _)
  unfold t at hx; rw [Real.rpow_sub hp] at hx
  have hh: x^(-(1/10):ℝ)/normedWidth x*c < b:=(lt_div_iff₀ hc).1 hx
  unfold normedWidth at hh; rw [div_mul_eq_mul_div,div_lt_iff₀ (Real.rpow_pos_of_pos hp _)] at hh; rw [mul_comm c]; apply hh.le.trans_eq; unfold b; ring
end rates
variable {S:Supply.Sheet G}{K:Rolls S}{Y:Protection K}{q v:ℝ} (g:G.Simple)
include g
lemma header (V:Delays Y)(hv:0<v)(q:ℝ):∃ Z:Delays Y,DelayLe V Z ∧ ∀ X:Delays Y,DelayLe Z X→∀ (P:Bar X)(W:Wait P)(a:Levels G), Paid W a→ Search a q v:=by
   let α j:= G.slopeConstant*Real.log (K.L j).val
   have hp (j:ℕ): 0< α j:= mul_pos (Gauge.slopeConstant_pos g) (Real.log_pos ?_) -- block need >1 check!
   ·
     obtain ⟨x,-,hb,hx⟩:= collect_upper V.betaEntry _ (fun j=> eventually_transitions j _ _ (fun i _=> ((trade G (S.profile i) (hp j) hv).and (Pass.yet.and ((tendsto_rpow_atTop (show 0<(1/256:ℝ) by norm_num)).eventually_ge_atTop (q/2))))))
     refine ⟨{V with betaEntry:=x},⟨hb,le_rfl,le_rfl,le_rfl⟩,fun L h X W a hz=> ?_⟩
     have hK i:= hx (a.clock.J (i+1)) _ ((h.beta _).trans (hz.pays i)) _ (step_paid a i);
     refine ⟨fun i=> (hK i).2.1,fun i=>(hK i).2.2,?_,?_⟩
     · intro i; rw [brace,brace,clipS (hK _|>.2.1.floor),clipS (hK _|>.2.1.floor)]; apply Real.rpow_le_rpow (hK _|>.2.1.floor.le) _ (by norm_num)
       induction i with
       | zero=>rfl
       | succ i ih=> rw [beta_eq hz]; exact ih.trans (le_add_of_nonneg_right (hp _|>.le))
     intro i; induction i with
       | zero=> rw [Finset.sum_range_zero]; exact mul_nonneg tintP.1.le (mul_nonneg (Pass.widthP (hK _|>.2.1.floor)).le (hK _|>.2.1.floor.le))
       | succ i ih=>
         rw [sum_range_succ]; have hu:= hK i|>.1; unfold stow fn brace; rw [params_eq hz,beta_eq hz,show (a.budget i).threshold=Instrument.plain.t (a.clock.hatBeta i) from (Deployment.clock_eqns a.clock i).2.2.2.2.2.2]
         refine (add_le_add ih hu).trans_eq ?_; unfold brace; unfold Pressure.betaF α; ring
   exact_mod_cast (show 1<(K.L j).val from lt_of_lt_of_le (by norm_num) (K.large j).size)
end YM.PhysicalNext.Repeat.Muse
