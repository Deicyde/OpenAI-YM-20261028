import YM.TraceExtension.Terrace.Fund
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG Wilson Labels Source MergeProof MergeProof.Accent Extra.Histories Bid Zn
open Extraction Next.UVStress Next.Rank.Price Next.Rank.East MergeProof.East Further.CorrectedLift Ward Climb Analysis StressFlux
open Further.PhysicalPeriodLimitF933 Work.D01 Work.G08 Next.Rank.Station
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G:Gauge}{C:Family G}
private lemma stage_logs (P:Levels G)(c:ℝ)(h:0 <c):∀ᶠ i in atTop,∀ j:ℕ,i ≤ j → Work.D01.columnLogs P j -Work.D01.columnLogs P i ≤ c*gap P i j:=by
    have hd : Tendsto (fun i : ℕ => ((P.clock.J (i+1):ℝ)^2)⁻¹) atTop (𝓝 0) := by
      have ht := P.fits.deep.comp (tendsto_add_atTop_nat 1); exact tendsto_inv_atTop_zero.comp
       ((tendsto_pow_atTop (n := 2) (by decide)).comp (tendsto_natCast_atTop_atTop.comp ht))
    obtain ⟨k,hk⟩:= eventually_atTop.mp (hd.eventually (ge_mem_nhds h))
    filter_upwards [eventually_ge_atTop k] with i hi j hj
    induction j,hj using Nat.le_induction with
    | base=> simp [gap]
    | succ j hv ih=>
       let p:=P.params (j+1); let z:= Real.log ((P.S.block j).val:ℝ); have he:0 < z:= zero_lt_one.trans_le ( (lowerQ P j).trans_eq (qNext P j))
       have hp: Real.log p.columns/z ≤ c:= le_trans ((Real.log_le_log (zero_lt_one.trans_le p.columns_ge) (show p.columns ≤ 1+p.paths+p.width⁻¹+p.columns+p.clip.relaxation+p.supportExponent by linarith only[p.paths_pos, inv_pos.mpr p.width_pos, p.clip.radius_pos, p.price_pos])|>.trans_eq rfl) |> fun h=> div_le_div_of_nonneg_right h he.le) ((P.fits.logCost j).trans (hk _ (hi.trans hv)))
       rw [columnLogs_succ,triangle P i j, qNext]; linarith only [ih,(div_le_iff₀ he).mp hp]
lemma crescent (P:Levels G)(c:ℝ)(θ:PostT P)(h:G.Simple)(ht:0<c):∀ᶠ i in atTop,∀ j:ℕ,i≤j → j ≤ summit P i→ Real.exp (columnLogs P j-columnLogs P i) ≤ watch P c i:=by
    filter_upwards [stage_logs P (c/2) (half_pos ht),back_gate _ h θ] with i he hv j hp hx
    refine Real.exp_monotone ((he j hp).trans ((mul_le_mul_of_nonneg_left ((mono_gap P i j hx).trans hv) (by linarith only[ht]:0 ≤ c/2)).trans_eq ?_)); ring
set_option quotPrecheck false
local notation "A"=> C.path.levels
variable (H:C.Makes) {N i p d j k:ℕ}
local notation "T!"=> C.labels.level d
include H
lemma ribbon_cost(hN:j≤N)(hk:C.ref d ≤ i)(ht:i ≤ j) (v:C.label d) : (T!).coeffSize (Cturn C d j N p v) ≤ Real.exp (columnLogs (A) j-columnLogs (A) i)*(T!).coeffSize (Cturn C d i N p v) :=by
   induction j,ht using Nat.le_induction with
   | base=> rw[sub_self,Real.exp_zero,one_mul]
   | succ j he IH=>
      let c:= ((A).params (j+1)).columns; have hc:0<c:= zero_lt_one.trans_le ((A).params _).columns_ge
      refine ((H.calibrated d N p ((hk.trans he).trans (j.le_succ.trans hN))).back j (hk.trans he) hN ((C.factory d N p).terminal.symm v)).trans ((mul_le_mul_of_nonneg_left (IH (by omega)) hc.le).trans_eq ?_)
      rw [columnLogs_succ, add_comm (columnLogs (A) j),add_sub_assoc, Real.exp_add,Real.exp_log hc,mul_assoc]

omit H in
lemma tiltP (b:ℝ){i:ℕ}(hp:b ≤ Next.Rank.Perch.y (C.path.levels.clock.hatBeta i)): mag (A) b i≤tilt_cap (A) i:=Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) hp
lemma ages_cost (T: Module.End ℂ (C.label d))(V: Tested C d k N p T)(hk:C.ref d ≤ k)(hn:k≤N)(v:C.label d)(hG:G.Simple)(ht:d≤5)(u:ℝ)(hp:1≤u): let a:=C.S.a k; let t:=(A|>.clock.monitor k); let L:= ladd C u k N p d T
     (T!).coeffSize (Cturn C d k N p (L v)) ≤ a^d*(2*((2*t)^2 * u^d))* (T!).coeffSize v:=by
   intro a t L; let y:=weightTag C d u v; let z:=shrink C k N p; have hy:0<z:=shrink_pos C H hn p; have he:T (L v)=(T!).scaled z⁻¹ y:=by unfold L ladd; rw[dif_pos (Tested.bijective C H hk hn T V)]; exact (LinearEquiv.ofBijective T (Tested.bijective C H hk hn T V)).apply_symm_apply _
   have hr:1 ≤ t:=Real.one_le_exp (sq_nonneg _)
   have h(w:C.label d): (T!).coeffSize ((T!).scaled z⁻¹ w) ≤ (2*t)^2*(T!).coeffSize w:=by
       have hK:z⁻¹ ≤ 2*t:=shrink_min C H hn p
       unfold Frame.coeffSize; rw[Finset.mul_sum]; refine Finset.sum_le_sum (fun i _=>?_); rw [Frame.scaled_apply,norm_mul,Complex.norm_real,Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr hy).le _)]; refine mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (inv_pos.mpr hy).le hK _).trans (pow_le_pow_right₀ (by linarith only[hr]) ?_)) (norm_nonneg _)
       by_cases hi:i=0; · rw[hi,(T!).zero_degree];decide
       exact (nbase (T!) ht i hi hG).2.2.le
   have hy : (T!).coeffSize y ≤ u^d*(T!).coeffSize v:=by unfold Frame.coeffSize;rw[Finset.mul_sum]; refine Finset.sum_le_sum (fun i _=>?_); unfold y weightTag; simp only [LinearMap.coe_mk,AddHom.coe_mk,norm_mul,Complex.norm_pow, Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hp)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp ((T!).bound _)) (norm_nonneg _)
   have hs:= V.cost C T (L v); rw [he] at hs; have hz := hs.trans (mul_le_mul_of_nonneg_left ((h _).trans (mul_le_mul_of_nonneg_left hy (sq_nonneg _))) zero_le_two)
   unfold awake at hz; rw[Size.smul,norm_inv,norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le] at hz; have hg:0<a:=C.S.a_pos _
   apply le_of_mul_le_mul_left _ (show 0 < (a^d)⁻¹ from by positivity); refine hz.trans_eq ?_; generalize (T!).coeffSize v = Q
   field_simp
lemma capacity_cost (d:ℕ)(ht:d≤5)(hG:G.Simple)(θ:PostT C.path.levels)(v:C.label d)(c:ℝ)(hc:0<c):∀ᶠ i:ℕ in atTop,∀ N p,summit C.path.levels i ≤ N →∀ (T:Module.End ℂ (C.label d)) (hv:Tested C d i N p T) (b:ℝ),1≤ b→ b ≤ tilt_cap C.path.levels i→∀ j:ℕ,i≤j→ j ≤ summit C.path.levels i → (C.labels.level d).coeffSize (Cturn C d j N p (ladd C b i N p d T v)) ≤ C.S.a i^d*watch C.path.levels c i:=by
    let P:= C.path.levels; let f:= C.labels.level d; let y i:= P.clock.monitor i
    have ht':Ticket P 0 y:= (favorite P hG).mono (( (hrate P hG).eventually (wave_sub 1 1 zero_lt_one)).mono (fun i h=>by
        have hp : y i= Wave 1 (P.clock.hatBeta i):=by unfold y Wave RLog Calendar.monitor; rw [one_mul]
        rw[hp];exact ⟨(wake ..).le, h.trans_eq (Real.rpow_one _)⟩))
    have he:Ticket P 0 (fun i=> 2*((2*y i)^2 * tilt_cap P i ^ d) * f.coeffSize v ):= ((sapTree hG P 2 zero_le_two).push ((((sapTree hG P 2 zero_le_two).push ht').pows hG 2).push ((titles P hG).pows hG d))).push (sapTree hG P _ (size_nonneg ..))
    filter_upwards [crescent P (c/2) θ hG (half_pos hc),he (c/2) (half_pos hc),eventually_ge_atTop (C.ref d)] with i hj hF hC N p hN T H' b hy hq j hm hk
    let a:= C.S.a i; let m:= tilt_cap P i; have hp: 0<a:=C.S.a_pos _; have hε: b^d ≤ m^d:= pow_le_pow_left₀ (zero_le_one.trans hy) hq _
    let W:=watch P (c/2) i; have hw: 0 ≤ W:=(Real.exp_pos _).le
    have hh: f.coeffSize (Cturn C d i N p (ladd C b i N p d T v)) ≤ a^d* W:=by
       apply (ages_cost H T H' hC ((hm.trans hk).trans hN) v hG ht b hy).trans; change a^d*(2*((2*y i)^2 * b^d))*_≤_ ; linarith only [mul_le_mul_of_nonneg_left hF.2 (pow_nonneg hp.le d),mul_le_mul_of_nonneg_right hε (mul_nonneg (mul_nonneg (pow_nonneg hp.le d) (size_nonneg f v)) (sq_nonneg (2* y i)))]
    refine (ribbon_cost H (p:=p) (hk.trans hN) hC hm _).trans ((mul_le_mul (hj _ hm hk) hh (size_nonneg ..) hw).trans_eq ?_); change W*(a^d*W)=_; rw [mul_left_comm]; unfold W;
    unfold watch; rw [← Real.exp_add]; apply congr_arg; congr 1; ring
end YM.Trace.Terrace
