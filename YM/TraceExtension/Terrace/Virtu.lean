import YM.TraceExtension.Terrace.Meteor
import YM.TraceExtension.Shunt.Ready
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux Pressure
open Further.PhysicalPeriodLimitF933 Shunt Weir
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}
def supportQ (Y:Levels G):Prop:= ∀ᶠ k:ℕ in atTop,4 ≤ (Y.params k).supportExponent
lemma oracle (P:Levels G)(k:ℕ): P.clock.monitor k=Wave 1 (P.clock.hatBeta k):=by unfold Wave RLog Calendar.monitor; rw[one_mul]
lemma Tanya (P:Levels G)(k:ℕ): (P.budget k).threshold=Swift.thetaP (P.clock.hatBeta k):=by
   change P.clock.threshold k=_; unfold Calendar.threshold; rw[oracle];rfl
lemma Harmony(P:Levels G)(k:ℕ): Weir.smoke (P.clock.hatBeta k)= P.clock.forcedAllowance k:=by unfold Weir.smoke Calendar.forcedAllowance; rw[oracle]
lemma quid_fee : Lim ((-1:ℝ)) Shunt.grantS:= ((tall.pow 2).prod (ferry (waveM _))).spot (by norm_num)
lemma book_pay (u:ℝ)(hu:0≤u):∀ᶠ x:ℝ in atTop,u*Shunt.grantS x ≤ 1∧ 4*(1+Real.log x)*(u*Shunt.grantS x) ≤ x^3:=by
   let f x:= u* Shunt.grantS x; have ht:Lim (-1) f:= by simpa only [zero_add] using (board hu).prod quid_fee
   let g(x:ℝ):= 4*(1+Real.log x)*f x
   have hT:Lim (-1) g:= by simpa only [zero_add] using! (board (show 0≤ (4:ℝ) by norm_num)|>.prod (ferry ((mass zero_le_one).gather logC))).prod ht
   filter_upwards [ht.tiny (by norm_num),hT.tiny (by norm_num),eventually_ge_atTop (1:ℝ)] with x ht hp hQ; exact ⟨ht,hp.trans (one_le_pow₀ hQ)⟩
lemma bias_pay (P:Levels G)(θ:PostT P)(h:G.Simple)(u:ℝ)(hx:0 ≤ u):∀ᶠ k in atTop, 4*(1+(P.params k).columns)*(u*Shunt.grantS (P.clock.hatBeta k))/ PhysicalNext.Repeat.Quince.cameo P k ≤
    (P.clock.threshold k)^2 * AgeK P (-(1/4:ℝ)) k :=by
    let f(x):= 4*(1+Real.log x)*u; have hf:ConstMass 0 f:=((((mass zero_le_one).gather logC).times 4 (by norm_num)).cop (mass hx))
    filter_upwards [(hrate P h).eventually (hf (1/12) (by norm_num))] with k hk; apply (div_le_iff₀ (PhysicalNext.Repeat.Quince.cameo_pos ..)).mpr
    let x:=P.clock.hatBeta k; let y:=P.clock.threshold k; let t(a):=AgeK P a k; have hp:4*(1+(P.params k).columns)*u ≤ t (1/12):= le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_right (θ.share k) _) (by positivity)) hx) hk.2
    have hu:Shunt.grantS x=y^ (2:ℕ)* (t (1/6)):=by unfold Shunt.grantS; change Swift.thetaP x^ (2:ℕ)*_= _; rw[← show y=Swift.thetaP x from Tanya P k];rfl
    have he:y^ (2:ℕ)*t (-(1/4:ℝ)) * PhysicalNext.Repeat.Quince.cameo P k=t (1/12)*Shunt.grantS x:=by
        rw [cameo_age, hu]; change y^ (2:ℕ)*_*_= t (1/12)*(y^ (2:ℕ)*_); unfold t; rw [mul_left_comm (AgeK ..),mul_assoc, AgeK_mul, AgeK_mul];norm_num
    rw [← mul_assoc]; apply (mul_le_mul_of_nonneg_right hp (show 0 ≤ Shunt.grantS x from hu ▸ mul_nonneg (sq_nonneg _) (wake ..|>.le))).trans_eq; exact he.symm
open PhysicalNext.Repeat.Quince
-- seam valuation.
lemma Meltdown (P:Levels G)(hp:supportQ P)(h:G.Simple): ∀ᶠ i in atTop, Melts 1 (P.budget i) (P.clock.hatBeta i)⁻¹ (P.clock.forcedAllowance i) (P.clock.hatBeta i)⁻¹:=by
   let q(x):= radiusB x
   let d(x:ℝ):= ((q x+q x+1)^4:ℕ)
   let r(x):= Extra.Multi.siteFactor (q x)
   let a(x):= Weir.smoke x; let t(x:ℝ):= a x + r x * Real.sqrt (a x)+x⁻¹+r x*x⁻¹
   have ha: Lim (-1) (fun x=>Real.sqrt (a x)):= by simpa using! oil 1 (relief 1)
   have hS:Lim (-1) a:= ha.down (by refine Eventually.of_forall fun x=>?_ ; have h: 0 < a x:=Real.exp_pos _; refine ⟨h.le,(Real.le_sqrt h.le h.le).2 ?_⟩; rw [sq]; exact mul_le_of_le_one_left h.le (show a x ≤ 1 from stares x|>.trans_le (Doors.stain_le ..)))
   have hI:Lim (-1) (fun x:ℝ=>x⁻¹):= by refine isomV (F:=fun x:ℝ=>x^(-(1:ℝ))) ?_ (sands _); simp only[Real.rpow_neg_one,Filter.EventuallyEq.rfl]
   have hr:Lim 0 r:=by
      unfold r Extra.Multi.siteFactor; refine ferry (a:=0) (ConstMass.times ?_ _ (Real.exp_pos _).le); refine ConstMass.crop ?_ 4; exact (( ((Zn.upperB.times 16 (by norm_num)).gather (mass (by norm_num)))).times 2 (by norm_num))
   have hd:Lim 0 (fun x=>(d x:ℝ)):=by unfold d;push_cast;exact ferry (((upperB.gather upperB).gather (mass zero_le_one)).crop 4)
   have ht:Lim (-1) t:= by unfold t; exact Lim.plus ( (hS.plus ((zero_add (-1:ℝ)) ▸ hr.prod ha)).plus hI) ((zero_add (-1:ℝ)) ▸ hr.prod hI)
   have hw : Tendsto t atTop (𝓝 0):=by
       have ht:= ht (-(1/2)) (by norm_num); exact squeeze_zero' (ht.mono fun _ i=>i.1) (ht.mono fun _ i=>i.2) (tendsto_rpow_neg_atTop (show 0 < (1/2:ℝ) by norm_num))
   have hu:= Real.continuous_exp.continuousAt.tendsto.comp hw; rw[Real.exp_zero] at hu
   have hv : ∀ᶠ x:ℝ in atTop,(d x:ℝ)*t x ≤ 1∧ Real.exp (t x)-1 ≤ 1:=by
      filter_upwards[(hd.prod ht).tiny (by norm_num),hu.eventually (ge_mem_nhds (show (1:ℝ)<2 by linarith))] with x hx h; refine ⟨hx,?_⟩; change Real.exp (t x) ≤ 2 at h; linarith only[h]
   filter_upwards[hp,(hrate P h).eventually hv] with i hi h;
   have he:1≤P.clock.hatBeta i:= (P.fits.delayed _).le; refine ⟨inv_pos.mpr (bell ..),inv_le_one_of_one_le₀ he, inv_nonneg.mpr (zero_le_one.trans he),hi,?_⟩
   dsimp only; rw [← Harmony P i]; simp only[Nat.cast_one,one_mul]; exact ⟨h.1.trans (by norm_num),h.2⟩
end YM.Trace.Terrace
