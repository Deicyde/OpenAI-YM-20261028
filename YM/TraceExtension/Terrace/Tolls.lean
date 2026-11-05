import YM.TraceExtension.Terrace.Casa
import YM.TraceExtension.Terrace.Terrain
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}
lemma mires(G:Gauge)(S:Stage) :∀ᶠ x:ℝ in atTop,∀ (n:Side)(R:Rep G n)(Λ:ℝ)(h:Age S x Λ R),
     Shepherd.tariff R (leaseC R S.width S.paths Λ) (hue x) ≤ x^3:=by
   let H(x:ℝ):= 4*x; let W:=Shepherd.wide G S.supportExponent; let Q:=Geo.lowerSize S.clip S.paths; let c:= W*momentPrice 1 (S.width/4)*Q; let f(x):= (2*thetaP x*H x)*c+(W*(H x*(thetaP x^3*S.paths+thetaP x^4*S.paths)+thetaP x^2*humble x)); let g(x):=Extra.Multi.siteFactor (radiusB x); let F(x):=Fintype.card Signed * g x*(VerifiedReset.factor*f x)+ hue x*g x;
   have hW:0 ≤ W:=(Real.exp_pos _).le; have hs:= S.paths_pos; have hQ:0 ≤ Q:=by unfold Q Geo.lowerSize; positivity [S.clip.quadratic_pos];
   have hz:S.width>0:= S.width_pos;have he:0 ≤ c:=mul_nonneg (mul_nonneg hW (momentPrice_pos _ (by positivity)).le) hQ;
   have hH:Lim 1 H:=by simpa only[Real.rpow_one,zero_add] using! (board (by norm_num:(0:ℝ) ≤ 4)).prod (sands 1)
   have hh:Lim 2 f:=by
      refine Lim.plus ?_ ?_
      · exact ((( ((board (show (0:ℝ)≤ 2 by positivity)).prod tall).prod hH).prod (board he))).spot (by norm_num)
      have h1:= ((hH).prod (((tall.pow 3).prod (board hs.le)).plus (((tall.pow 4).prod (board hs.le)).spot (by norm_num))))
      exact ((board hW).prod (h1.plus ((((tall.pow 2).prod (ferry h_mass))).spot (by norm_num)))).spot (by norm_num)
   have hg: ConstMass 0 g:=by unfold g Extra.Multi.siteFactor; exact (mass (Real.exp_pos _).le).cop ((((upperB.times 16 (by norm_num)).gather (mass (by norm_num))).times _ (by norm_num)).crop _)
   have hF:Lim 2 F:=by refine ((( ((board (Nat.cast_nonneg (Fintype.card Signed))).prod (ferry hg)).prod ((board VerifiedReset.factor_pos.le).prod hh))).spot (by norm_num) |>.plus ?_); exact (chime.prod (ferry hg)).spot (by norm_num)
   filter_upwards [hF 3 (by norm_num),eventually_gt_atTop (1:ℝ)] with x hv hx n R v h; have hθ:0 < thetaP x:=h.thresh ▸ R.p.threshold_pos
   apply le_trans _ (hv.2.trans_eq (Real.rpow_ofNat ..)); unfold F f g Shepherd.tariff leaseC bedste Shepherd.crown; rw[h.hM.1,h.thresh,h.hM.2.1,h.depth]; have hV:0≤ v:= Cost.nonneg h.good.paths.two; dsimp only [W,Q,c,H]; gcongr <;> first|exact h.beta|exact h.bnd|unfold Extra.Multi.siteFactor <;> positivity|positivity[VerifiedReset.factor_pos]
end YM.Trace.Weir

namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Pressure Weir Shepherd Push.GridApprox Next.Rank.Price
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
/-- support budget price and cancellation strip. exponent counts (not powers of lattice
 spacing); no factor proportional to number of copies. -/
def wheelQ (x:ℝ):= towerH x 60
def prism (x:ℝ):= towerH x 40
lemma bsize_c : ∀ᶠ x:ℝ in atTop,4*(prism x)≤ wheelQ x:=by
    unfold prism wheelQ towerH; filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 32] with x hx
    let B:= radiusB x; have hu: 1 ≤ B:=by omega
    have h:3300 ≤ B^40:= le_trans (by decide: 3300≤(32:ℕ)^3) ((Nat.pow_le_pow_left hx 3).trans (pow_le_pow_right₀ hu (show 3≤40 by decide)))
    have hh:32*B^40 ≤ B^60:=by apply le_trans (Nat.mul_le_mul_right (B^40) hx); change B*B^40 ≤_; rw [← pow_succ']; exact pow_le_pow_right₀ hu (show 41 ≤60 by decide)
    change 4*(B^40+1100) ≤ B^60+1100;linarith only[h,hh]
lemma growthP : Tendsto prism atTop atTop:=by refine tendsto_atTop_mono (g:=prism) (fun i=>Nat.le_add_right (radiusB i^40) 1100) ?_; exact (tendsto_pow_atTop (n:=40) (by decide)).comp Work.E01.radiusB_tendsto
lemma littleA (x:ℝ)(h:1 ≤ x): Terrace.Gate x ≤ (radiusB x:ℝ)^24:= calc
    _ = (Real.log x ^2)^24:=by unfold Terrace.Gate; ring
    _ ≤ _:=pow_le_pow_left₀ (sq_nonneg (Real.log x)) (Nat.le_ceil _) _
lemma petite : ∀ᶠ x:ℝ in atTop,(Real.log x) ≤ (radiusB x:ℝ):=by
   filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ)] with x hx
   exact le_trans (b:= Real.log x ^2) (by nlinarith only[hx]) (Nat.le_ceil _)
lemma hugeW (a:ℝ)(hp:0 ≤ a) :∀ᶠ x:ℝ in atTop, a*Gate x *Real.log x ≤ (prism x:ℝ)/32 :=by
   let B(x:ℝ):=(radiusB x:ℝ); have hx:Tendsto B atTop atTop:= tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto
   filter_upwards [ hx.eventually_ge_atTop (32*a),hx.eventually_ge_atTop 1,eventually_gt_atTop (1:ℝ),petite] with x hx h1 hh hB
   let y:= B x; have ht := gate_le x hh
   have hy:0≤ y:=zero_le_one.trans h1
   have hs: Gate x*Real.log x ≤ y^25:=by refine (mul_le_mul (littleA x hh.le) hB (Real.log_pos hh).le (pow_nonneg hy 24)).trans_eq ?_; rw [← pow_succ]
   rw[mul_assoc]; unfold prism towerH; push_cast; change _ ≤ (y^40+_)/_
   linarith only[mul_le_mul_of_nonneg_right hx (pow_nonneg hy 25), pow_le_pow_right₀ h1 (show 26 ≤40 by decide),mul_le_mul_of_nonneg_left hs hp]
lemma gardenP(c:ℝ)(k:ℕ):∀ᶠ x:ℝ in atTop,c*x^k ≤ Real.exp ((prism x:ℝ)/32):=by
    by_cases h: c ≤0
    · filter_upwards [eventually_gt_atTop (1:ℝ)] with x hx;exact (mul_nonpos_of_nonpos_of_nonneg h (by positivity)).trans (Real.exp_pos _).le
    have hc:0<c:=lt_of_not_ge h
    have hz:Tendsto (fun x=>(prism x:ℝ)/64) atTop atTop:= (tendsto_natCast_atTop_atTop.comp growthP).atTop_div_const (by norm_num : (0:ℝ)<64)
    filter_upwards [hz.eventually_ge_atTop (Real.log c), hugeW (2*k:ℝ) (by positivity), Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_gt_atTop (1:ℝ)] with x hQ hA ht hx
    let L:= Terrace.Gate x; have h: 1 ≤ L:= one_le_pow₀ ht
    have hp : Real.log c+k*Real.log x≤ (prism x:ℝ)/32:=by linarith only[hA,hQ,mul_le_mul_of_nonneg_left h (show 0 ≤ (k:ℝ)*Real.log x from mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans ht))]
    exact (le_trans (le_of_eq (b:=Real.exp (Real.log c+k*Real.log x)) (by rw[Real.exp_add,Real.exp_nat_mul, Real.exp_log hc, Real.exp_log (by positivity)])) (Real.exp_monotone hp))
lemma Dsmall : ∀ᶠ x:ℝ in atTop, 2*Real.exp (prism x)*Weir.smoke x ≤ Real.exp (-(prism x:ℝ)/8):=by
    filter_upwards [( ((bankH 40).times 4 (by norm_num)) (1/5) (by norm_num)), growthP.eventually_ge_atTop 1] with x hx ht
    let t:ℝ:=prism x; have hX:1 ≤t:=by unfold t; exact_mod_cast ht
    have he: Weir.smoke x=Real.exp (-(Wave (1/5) x)):=by unfold smoke Swift.fog; rw[wring,one_mul]
    calc
       _ ≤ Real.exp t * Real.exp t * Weir.smoke x:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_trans Real.exp_one_gt_two.le (Real.exp_monotone hX)) (Real.exp_pos t).le) (Real.exp_pos _).le
       _ ≤ _:=by rw[he,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone; linarith only [ (show 4*t ≤ Wave (1/5) x from hx.2), hX]
end YM.Trace.Terrace
