import YM.TraceExtension.Quince.Glee
import YM.Extra.ITERATION_NO_LOSS.Scales
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Opals
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Quince
open Function Filter Set Lattice Wilson RG Pressure Stores Precision
open Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Exterior Bloch Planned.AtomRegular JointLoad JointLoad.Heir
open Push Push.AbsoluteSums Gas Ovens ConnectedActivityE6 Coat Brim Cub Extra.Iteration Extra.Iteration.Scales Malachite
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
open Next.Scheduling Supply Lute Push.SectorMeasure AnalyticBridge.LocalGaussian
variable {G:Gauge}{n:ℕ}{t:ℝ}{f: Side}
section tall
variable (C:Libretto G n)(D:Record)(L:Side)(p r:ℕ)
private def hail (x:ℝ):=bulk (packing L x) r x
local notation "w0" => Delay.fineMonitor G L
private lemma hasty : Tiny (bankP G L) (hail L r):=by
     have hp:=wire G L; have ht:=swell G L; exact (((Tiny.const ht (r+48:ℝ) (by positivity)).mul hp ht).mul ((Tiny.const ht 1 (by positivity)).add (stacking G L) ht) ht)
private lemma hale : Rate G L 0 (hail L r) :=by
    unfold hail bulk; simpa only[zero_add] using! ((((Rate.const 1).add (Rate.radius_price (G:=G) (L:=L))).mul_left ((r+48):ℝ)).mul ((Rate.const 1).add (stackingW G L)))
private def aprice (x:ℝ):= boost C D L *hail L r x^Lute.fuse n p+16/D.ε
private lemma aprate : Rate G L 0 (aprice C D L p r):=by unfold aprice; exact (Rate.add (by simpa only [zero_mul] using (((hale (G:=G) L r).pow (Lute.fuse n p)).mul_left (boost C D L))) (Rate.const _))
private lemma apaid : Tiny (bankP G L) (aprice C D L p r):=by unfold aprice; have hp:=swell G L; exact ((Tiny.mul (Tiny.const hp (boost C D L) (boost_nn ..)) ((hasty (G:=G) L r).pow hp _) hp).add (Tiny.const hp _ (by have h:=D.guards; positivity)) hp)
private lemma gkeeper : ∀ᶠ x:ℝ in atTop,∀ β,betaF G x L /2 ≤ β → 0< gStep β ∧ gStep β ≤ 2*(Real.sqrt (betaF G x L))⁻¹:=by
    filter_upwards [Delay.shift_pos G L] with x hx β hβ; have hp:0<β:=by linarith
    have ht:=Real.sqrt_pos.mpr hp
    have he:gStep β=(Real.sqrt β)⁻¹:=rfl
    rw[he]; refine ⟨inv_pos.mpr ht,?_⟩; have hz:=Real.sqrt_pos.mpr hx; rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ ht,div_mul_eq_mul_div,le_div_iff₀ hz]; nlinarith [Real.sq_sqrt hp.le,Real.sq_sqrt hx.le]
def samite (x:ℝ):= clinicFee n D.Q*(2*C.C*(1+(radiusD x:ℝ))^p)^2
private def uval (x:ℝ):=(aprice C D L p r x + samite C D p x)*fiery G x L+(aprice C D L p r x * 2+2)/(bankP G L x)
def straps (x:ℝ):= 1+Lute.guests G D.K (n+1) L*hail L r x^Lute.visitors (n+1)
private lemma march_δ:fRate G L (fun x=> uval C D L p r x*straps (G:=G) (n:=n) D L r x):=by
   let W:= straps (G:=G) (n:=n) D L r; let q:=aprice C D L p r
   have ht:=swell G L; have hv:= hasty (G:=G) L r; have hW:Tiny (bankP G L) W:= by unfold W straps; exact (Tiny.const ht 1 (by positivity)).add ((Tiny.const ht _ (guest_nn ..)).mul (hv.pow ht _) ht) ht
   have hw: Rate G L 0 W:=by unfold W straps; apply Rate.add (Rate.const _); simpa only [zero_mul] using (((hale (G:=G) L r).pow _).mul_left (Lute.guests G D.K (n+1) L))
   have hx:= (aprate C D L p r); have he:= apaid C D L p r; have hT: Rate G L 0 (samite C D p):=by
        unfold samite; simpa only [zero_mul] using (((hRate (p:=p) (G:=G) (L:=L) |>.mul_left _).pow 2).mul_left _)
   unfold uval; simp_rw [add_mul,div_mul_eq_mul_div,add_mul]; apply fRate.inn (v:=fun x=> (aprice C D L p r x*2*W x+2*W x)/(bankP G L x))
   · apply fGood (a:=-(1/2)) _ (by norm_num);
     apply Rate.add<;> first | simpa only[zero_add,add_zero] using (hx.mul Rate.flame|>.mul hw) | simpa only [zero_add,add_zero] using (hT.mul Rate.flame|>.mul hw)
   apply fum; apply Tiny.add _ _ ht; · exact ((he.mul (Tiny.const ht 2 (by positivity)) ht).mul hW ht)
   exact (Tiny.const ht 2 (by positivity)).mul hW ht
private lemma horizon_u(x:ℝ)(β:ℝ){f:Side}(X:Support f)(P B:BudgetPoint)(ht:B.threshold=fiery G x L)(he:P.threshold ≤ 2*B.threshold)(hK:B.B ≤ 2*radiusB x)(hp: P.power=p)(h:coverNumber B.B X≤packing L x)(hs: 0< betaF G x L)(hm:0<gStep β)(hh:gStep β≤ 2*(Real.sqrt (betaF G x L))⁻¹): opalW C D P B (radiusD x) L X r x (gStep β) ≤ uval C D L p r x:=by
   let u:= gStep β; let F:= B.threshold; let l(x:ℝ):=aprice C D L p r x
   have hF:=B.threshold_pos; have h':=boost_nn C D L; have hy:=D.guards; have hY:=zero_le_one.trans C.C_one; have hz:= add_nonneg hF.le (div_nonneg hm.le hF.le)
   have hv : u/F ≤ 2/bankP G L x:=by
        unfold F; rw[ht]; apply (div_le_div_of_nonneg_right hh (temp_nonneg _)).trans_eq; unfold temp; let v:= Real.sqrt (betaF G x L); have h1: 0<v:=Real.sqrt_pos.mpr hs
        change 2*v⁻¹/(v⁻¹*w0 x) = _; have hg:=Delay.monitor_pos G L x; unfold bankP; field_simp
   have hP:= bulk_one (coverNumber B.B X) r x; have hb : bulk (coverNumber B.B X) r x ≤ hail L r x:= by unfold bulk hail bulk; gcongr
   have ha : opal C D P B L X r x u ≤ aprice C D L p r x*(F+2/bankP G L x):=by
       unfold opal aprice; rw [add_mul]; have hD: ζ B u ≤ F + 2/bankP G L x:= add_le_add_right hv _
       refine add_le_add ((booster (C:=C) (D:=D) hK he (show u≥0 from hm.le)).trans ?_) ?_
       · rw [hp, mul_right_comm _ (ζ B u)]; have hq:= hP.trans hb; gcongr
       gcongr
   have hq:= mul_nonneg (by norm_num : (0:ℝ)≤2) (zero_le_one.trans D.majorant)|>.trans (clinicFee_le n (zero_le_one.trans D.majorant))
   have hpz : paintW C D P B (radiusD x) u ≤ samite C D p x*F +2/bankP G L x:=by
       unfold paintW; rw [add_div]; refine add_le_add ?_ hv; rw[div_le_iff₀ hF]; unfold samite
       apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by unfold loom; have ht:=P.threshold_pos; positivity) (show loom P (radiusD x) C.C ≤ C.C*(2*B.threshold)*(1+(radiusD x:ℝ))^p by unfold loom; rw [hp];gcongr) 2) hq)
       unfold F; ring_nf; rfl
   apply (add_le_add ha hpz).trans_eq; unfold uval F; rw [ht]; ring
lemma scales_m (y:ℝ)(hy:0<y):∀ᶠ x:ℝ in atTop,∀ β:ℝ, betaF G x L/2 ≤ β → ∀ (f:Side)(X:Support f)(P B:BudgetPoint),B.threshold=fiery G x L → P.threshold ≤ 2*B.threshold → B.B≤2*radiusB x→P.power=p → coverNumber B.B X ≤ packing L x →
    let F:=opalW C D P B (radiusD x) L X r x (gStep β); F≤1 ∧ ∀ t:ℝ,0≤t →clocks C t * F * Moments.meter (Lute.heads G B L X r x) 0 D.K (2*((n+1)+(n+1))) ≤ y/(coinP G L x)*t:=by
   let W(x):= uval C D L p r x; let K:= straps (G:=G) (n:=n) D L r
   let d:=clocks C 1+1; have hi:0≤clocks C 1:=clocks_pos _ zero_le_one; have hD:0<d:=by unfold d; positivity
   have hL : fRate G L (fun x=>W x*K x):= march_δ C D L p r
   filter_upwards [ (swell G L).eventually_ge_atTop 1, gkeeper (G:=G) L, Delay.shift_pos G L, hL.eventually (ge_mem_nhds (show (0:ℝ)<1 from zero_lt_one)), (show Tendsto (fun x=> d*(coinP G L x*(W x*K x))) atTop (𝓝 0) from mul_zero d ▸ (hL.const_mul d)).eventually (ge_mem_nhds hy) ] with x hq hk hx hr hh β hβ f X P B ht he hK hp h F
   have hb:= horizon_u C D L p r x β X P B ht he hK hp h hx (hk β hβ).1 (hk β hβ).2
   have he: 0≤ W x := (opalW_nn C D P B (radiusD x) L X r x _ (hk β hβ).1.le).trans hb
   have hs := Lute.guest_nn G L (n+1) D; let z:= bulk (coverNumber B.B X) r x; have hu: z≤ hail L r x:= by unfold z hail bulk; gcongr
   have hw:1 ≤ K x:= le_add_of_nonneg_right (mul_nonneg hs (pow_nonneg ((zero_le_one.trans (bulk_one ..)).trans hu) _))
   have hg:1≤ coinP G L x:=Real.one_le_sqrt.mpr hq
   constructor
   · apply hb.trans; linarith only [show coinP G L x*(W x*K x) ≤1 from hr, le_mul_of_one_le_right he hw, le_mul_of_one_le_left (mul_nonneg he (zero_le_one.trans hw)) hg]
   intro t hν
   let m:= Moments.meter (Lute.heads G B L X r x) 0 D.K (2*((n+1)+(n+1))); have hm : m ≤ K x:=by
       apply (fares (r:=r) (L:=L) (X:=X) hK).trans; apply le_trans _ (le_add_of_nonneg_left zero_le_one); exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans (bulk_one ..)) hu _) hs
   have hE:= clocks_pos C hν
   have hQ: clocks C t≤ t*d:=by have he : clocks C t=t*clocks C 1:=by unfold clocks devBill reachBill;ring
                                rw [he];gcongr; unfold d; linarith
   have H':0≤ m:=by unfold m Moments.meter Moments.inflate; positivity [D.peak]
   have hw' : d*(W x*K x)≤ y/(coinP G L x):=by
       rw[le_div_iff₀ (by positivity)]; calc
          _ = d*(coinP G L x*(W x*K x)):=by ring
          _ ≤ _:= hh
   apply (mul_le_mul (mul_le_mul hQ hb (opalW_nn _ _ _ _ _ _ _ _ _ _ (hk β hβ).1.le) (mul_nonneg hν hD.le)) hm H' (by positivity :0 ≤ t*d*W x)).trans; nlinarith only [mul_le_mul_of_nonneg_right hw' hν]
end tall
end YM.PhysicalNext.Repeat.Quince
