import YM.TraceExtension.Terrace.Base
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Terrace
open Function Filter Set Lattice RG RG.Supply Wilson Push.PriceCompiler Push.GridApprox Vac
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}(A:Levels G) {i j k:ℕ}
lemma hrate (h:G.Simple) : Tendsto A.clock.hatBeta atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
lemma lrate (h:G.Simple): Tendsto (Lyra A) atTop atTop:= Real.tendsto_log_atTop.comp (hrate A h)
lemma grate(h:G.Simple): Tendsto (fun i=> Gate (A.clock.hatBeta i)) atTop atTop:= (tendsto_pow_atTop (show 48≠ (0:ℕ) by norm_num)).comp (lrate A h)
lemma Gate_calm : Tendsto (fun x=> Gate x/x) atTop (𝓝 0):= (Real.isLittleO_pow_log_id_atTop (n:=48)).tendsto_div_nhds_zero
lemma Lyra_small(d:ℕ){c:ℝ}(hc:0<c): ∀ᶠ x:ℝ in atTop,(Real.log x)^d ≤ Zn.Wave c x:= (Zn.logC.crop d _ hc).mono fun x h=> h.2
lemma gate_le: ∀ x:ℝ,1<x→0<Gate x:= fun x h=> pow_pos (Real.log_pos h) _
lemma bell (t:ℕ): 0 < A.clock.hatBeta t:= zero_lt_one.trans (A.fits.delayed t)
lemma lira (t:ℕ): 0 < Lyra A t:= Real.log_pos (A.fits.delayed t)
lemma triangle(i j k:ℕ): gap A i k=gap A i j+gap A j k:=by unfold gap; ring
lemma qNext(j:ℕ): gap A j (j+1)=Real.log (A.S.block j).val:=by unfold gap;rw [A.S.scale_succ]; ring
lemma lowerQ(j:ℕ): 1 ≤ gap A j (j+1):=by
   rw[qNext]
   apply (Real.le_log_iff_exp_le (Nat.cast_pos.mpr ((A.S.block j).property): 0 < ((A.S.block j).val:ℝ))).mpr
   exact (Real.exp_one_lt_d9.le.trans (le_trans (by norm_num : (2.7182818286:ℝ) ≤ 3) (Nat.cast_le.mpr (A.S.block_large j))))
lemma bound_gap (hi:i ≤ j): (↑(j-i):ℝ) ≤ gap A i j:=by
    induction j,hi using Nat.le_induction with
    | base=>simp [Nat.sub_self,gap,sub_self,Nat.cast_zero]
    | succ j h IH=> rw [triangle A i j,show j+1-i=j-i+1 by omega]; push_cast; exact add_le_add IH (lowerQ ..)
lemma mono_gap (i j:ℕ) {l:ℕ}(h:j≤l): gap A i j ≤ gap A i l:=by
   rw [triangle A i j l]; exact le_add_of_nonneg_right ((Nat.cast_nonneg _).trans (bound_gap A h))
lemma stamps (i j:ℕ): A.clock.hatBeta j=A.clock.hatBeta i+G.slopeConstant*gap A i j:=by unfold Calendar.hatBeta gap; change A.clock.bar+_*A.S.scale j=_+_*_; ring
lemma monoBeta (h:G.Simple): Monotone A.clock.hatBeta:=by intro i j hi; rw [stamps A i j]; exact le_add_of_nonneg_right (mul_nonneg (Gauge.slopeConstant_pos h).le ((Nat.cast_nonneg _).trans (bound_gap _ hi)))
lemma lypos(h:G.Simple): Monotone (Lyra A):= fun i j h'=> Real.log_le_log (bell A i) (monoBeta _ h h')
lemma exponent_gate (c:ℝ)(d:ℕ)(e:ℕ)(hp:0<c):∀ᶠ x:ℝ in atTop,x^d*(Real.log x)^e≤Real.exp (c*Gate x) :=by
    have ht: ∀ᶠ y:ℝ in atTop,(2*↑(d+e))* y ≤ c*y^48:=by
       let t:ℝ :=2*(↑(d+e):ℝ); filter_upwards [((tendsto_pow_atTop (n:=47) (by decide) (α:=ℝ)).const_mul_atTop hp).eventually_ge_atTop t,eventually_gt_atTop (0:ℝ)] with y hx hv
       exact (mul_le_mul_of_nonneg_right hx hv.le).trans_eq (by rw[mul_assoc,←pow_succ])
    filter_upwards [Real.tendsto_log_atTop.eventually ht,eventually_gt_atTop (1:ℝ)] with x hx hi
    have he:= Real.log_pos hi
    calc
     _ ≤ x^d * x^e := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he.le (Real.log_le_self (by positivity)) _) (by positivity)
     _ = Real.exp ((↑(d+e):ℝ)*Real.log x):=by rw [←pow_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
     _ ≤ _:=by apply Real.exp_monotone; refine le_trans ?_ hx; have h : 0 ≤ (↑(d+e):ℝ):= Nat.cast_nonneg _; nlinarith only [he,h]

lemma back_gate (h:G.Simple)(θ:PostT A):∀ᶠ i:ℕ in atTop,gap A i (summit A i) ≤ 2*Gate (A.clock.hatBeta i):=by
   let s:= G.slopeConstant; have hs:0<s:=Gauge.slopeConstant_pos h
   have hz:∀ᶠ x:ℝ in atTop, s*Gate x ≤ x:=by
       filter_upwards [ (Gate_calm.const_mul s).eventually (ge_mem_nhds (by simp : s*0 < (1:ℝ))), eventually_gt_atTop (1:ℝ)] with x hx hw
       have hv := (show s*(Gate x /x) ≤ 1 from hx); rw [← mul_div_assoc,div_le_one₀ (by positivity)] at hv; exact hv
   have hw:∀ᶠ x:ℝ in atTop, Real.log (2*x) ≤ Gate x:=by
       filter_upwards [ Real.tendsto_log_atTop.eventually_ge_atTop (2:ℝ), eventually_gt_atTop (1:ℝ)] with x hx hp
       rw [Real.log_mul two_ne_zero (by positivity)]
       have hk : Real.log (2:ℝ)≤2:=Real.log_le_self zero_le_two
       refine le_trans (b:= Real.log x ^2) ?_ ?_
       · nlinarith only[hx,hk]
       exact pow_le_pow_right₀ (by linarith) (by decide)
   filter_upwards [(hrate A h).eventually hz,(hrate A h).eventually hw] with i hx hw
   have hQ:= stellar A i; obtain ⟨j,hY⟩:= Nat.exists_eq_succ_of_ne_zero (show summit A i ≠ 0 by omega)
   have hj:i ≤ j := by omega
   let x:= A.clock.hatBeta i; have hp: gap A i j ≤ Gate x:=by
       obtain hj|hj:= lt_or_eq_of_le hj; swap; · subst j; rw [gap,sub_self]; exact (gate_le x (A.fits.delayed _)).le
       exact le_of_not_ge (fun h'=> by have ht : summit A i≤ j:= Nat.find_min' _ ⟨hj,h'⟩; omega)
   rw [hY]; rw [triangle A i j,qNext]; have he : Real.log (A.S.block j).val ≤ Gate x:=by
       have hm:A.clock.hatBeta j ≤ 2*x:=by rw [stamps A i]; have hr : s * Gate x ≤ x:= hx; linarith only [mul_le_mul_of_nonneg_left hp hs.le,hr]
       apply le_trans _ hw; exact (Real.log_le_self (Nat.cast_nonneg _)).trans ((θ.bloom _).trans (Real.log_le_log (bell A j) hm))
   linarith only[hp,he]
lemma bond (h:G.Simple)(θ:PostT A) :∀ᶠ i:ℕ in atTop,A.clock.hatBeta (summit A i) ≤ 2*A.clock.hatBeta i∧ Lyra A (summit A i) ≤ 2*Lyra A i∧ ((A.clock.coverSize (summit A i):ℕ):ℝ) ≤ 5*Lyra A i^2:=by
    let s:= G.slopeConstant; have hs:0<s:=Gauge.slopeConstant_pos h
    have hB:∀ᶠ x:ℝ in atTop, s*(2*Gate x) ≤ x:=by filter_upwards [(Gate_calm.const_mul (2*s)).eventually (ge_mem_nhds (by simp : (2*s)*0<1)),eventually_gt_atTop (0:ℝ)] with x h hp; have hh: (2*s)*(Gate x/x)≤ 1:=h; rw [← mul_div_assoc,div_le_one₀ hp] at hh; linarith
    filter_upwards [(hrate A h).eventually hB,back_gate A h θ, (lrate A h).eventually_ge_atTop (2:ℝ)] with i hh he hl
    let x:= A.clock.hatBeta i; let y:= Lyra A i; let t:= summit A i; have hx:0<x:=bell ..
    have hz:A.clock.hatBeta t ≤ 2*x:=by
       rw [stamps A i]; change x+s*gap A i t≤_; have hj:s*(2*Gate x)≤ x:=hh; linarith only [hj, mul_le_mul_of_nonneg_left he hs.le]
    have hv: Lyra A t ≤ 2*y:=by
       have he := (Real.log_le_log (bell ..) hz); rw[Real.log_mul two_ne_zero hx.ne'] at he; change Lyra A t ≤ Real.log 2+y at he; linarith only [he,(show 2 ≤ y from hl),Real.log_le_self (show 0 ≤ (2:ℝ) by norm_num)]
    refine ⟨hz,hv,?_⟩; have hL := lira A t; have hh : ((A.clock.coverSize t:ℕ):ℝ)≤ Lyra A t^2 +1:= (Nat.ceil_lt_add_one (sq_nonneg _)).le; change ((A.clock.coverSize t:ℕ):ℝ) ≤ 5*y^2; have hσ:2≤ y:=hl; nlinarith only [hh,hL,hv,hσ]
lemma ladder (A:Levels G)(h:G.Simple) : Monotone A.clock.coverSize:= fun i j h'=> Nat.ceil_mono (pow_le_pow_left₀ (lira A i|>.le) (lypos A h h') _)
lemma z_scale (i j:ℕ): A.S.a i/A.S.a j= Real.exp (gap A i j):=by simp only[gap,Schedule.scale,Real.log_inv]; rw[neg_sub_neg,Real.exp_sub,Real.exp_log (A.S.a_pos _),Real.exp_log (A.S.a_pos _)]
end YM.Trace.Terrace
