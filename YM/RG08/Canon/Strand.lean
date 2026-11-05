import YM.RG08.Canon.Stadium
/-! # Fixed period expansions with moving critical point

 Expand in the normal direction at the same tangential (scalar along path) point.
 Proof by uniform derivative control in a small product neighborhood.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open Function YM.PertExtension.Series.Radial YM.PertExtension.Chart RG08.Reflect Finset
open scoped BigOperators Topology Real ContDiff Classical
variable {V : Type*} [NormedAddCommGroup V][NormedSpace ℝ V]
variable (F : V × ℝ → ℝ)
private lemma jet_fit_1 {G : ℝ→ℝ→ℝ} (h : ContDiffAt ℝ ω (uncurry G) (0,0)) (i : ℕ) :
    ContDiffAt ℝ ω (uncurry (fun x=> iteratedDeriv i (G x))) (0,0) := by
  induction i with
  | zero=> simpa using h
  | succ i IH=>
     simp only [iteratedDeriv_succ]
     let K x:=iteratedDeriv i (G x)
     change ContDiffAt ℝ ω (fun p:ℝ×ℝ=> fderiv ℝ (K p.1) p.2 1) (0,0)
     exact ((Work.F05.curve_partial (F:=K) IH).clm_apply contDiffAt_const)
lemma strands_fit (x : V) (h : ContDiffAt ℝ ω F 0) (i : ℕ) : ContDiffAt ℝ ω (fun t:ℝ=> jet (fun u:V=> F (u,t)) i x) 0 := by
  let G t (r:ℝ):= F (r • x,t); let Q:=uncurry fun t=> iteratedDeriv i (G t)
  have hg : ContDiffAt ℝ ω (uncurry G) (0,0) := by
    exact (show ContDiffAt ℝ ω F ((0:ℝ) • x, (0:ℝ)) from by simp only [zero_smul]; exact h).comp (f:=fun p:ℝ×ℝ=> (p.2•x,p.1)) _ ((contDiffAt_snd.smul contDiffAt_const).prodMk contDiffAt_fst)
  have hp := jet_fit_1 hg i
  refine (show ContDiffAt ℝ ω (fun t:ℝ=> ((Nat.factorial i:ℝ))⁻¹*Q (t,0)) 0 from contDiffAt_const.mul (hp.comp (f:=fun t=>(t,0)) _ (contDiffAt_id.prodMk contDiffAt_const))).congr_of_eventuallyEq ?_
  have hv : Tendsto (fun t:ℝ=> ((0:V),t)) (𝓝 0) (𝓝 0):= tendsto_const_nhds.prodMk_nhds tendsto_id
  filter_upwards [hv.eventually (h.eventually (by simp))] with t ht; exact homogeneous_derivative _ x _ ((ht.comp (f:=fun u:V=> (u,t)) _ (contDiffAt_id.prodMk contDiffAt_const)).of_le le_top)

private lemma plow (n : ℕ) (F : V→ℝ) (h : ContDiffAt ℝ ω F 0) (x : V) {t : ℝ}(ht:0<t) : taylorWithinEval (fun r:ℝ=> F (r•x)) n (Icc 0 t) 0 t =
    ∑ i ∈ Finset.range (n+1), t^i*jet F i x := by
  let g (r:ℝ):= F (r•x)
  have hx : ContDiffAt ℝ ω g 0 := (show ContDiffAt ℝ ω F ((0:ℝ)•x) by simpa using h).comp (f:=fun r:ℝ=>r•x) 0 (contDiffAt_id.smul contDiffAt_const)
  have hp i : iteratedDerivWithin i g (Icc 0 t) 0 = iteratedDeriv i g 0 := by
    rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv_eq_iteratedFDeriv,iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_Icc ht) (hx.of_le le_top) (by exact ⟨le_rfl,ht.le⟩)]
  induction n with
  | zero=> simp
  | succ n ih=>
     rw [taylorWithinEval_succ,ih,sum_range_succ _ (n+1), show iteratedDerivWithin _ _ _ _ = _ from hp (n+1), homogeneous_derivative F x _ (h.of_le le_top)]
     simp only [sub_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,smul_eq_mul]; unfold g; ring

lemma strand (x : V) (z : ℝ) (h : ContDiffAt ℝ ω F 0) (i : ℕ) :
    Fit (i+1) (fun t:ℝ=> F (t • x,t*z)) (year (fun j t=> jet (fun u:V=> F (u,t*z)) j x) i) := by
  let G t (r:ℝ) := F (r • x,t*z)
  have hg : ContDiffAt ℝ ω (uncurry G) (0,0) := (show ContDiffAt ℝ ω F ((0:ℝ) • x, (0:ℝ)*z) from by simp only [zero_smul,zero_mul]; exact h).comp (f:=fun p:ℝ×ℝ=> (p.2•x,p.1*z)) _ ((contDiffAt_snd.smul contDiffAt_const).prodMk (contDiffAt_fst.mul contDiffAt_const))
  let P:= uncurry fun t=> iteratedDeriv (i+1) (G t)
  have hp : ContDiffAt ℝ ω P (0,0):=jet_fit_1 hg _; let M:=‖P (0,0)‖+1
  obtain ⟨d,hd,H⟩:=Metric.mem_nhds_iff.mp ((hg.eventually (by simp)).and (hp.continuousAt.norm.eventually_lt continuousAt_const (show ‖P (0,0)‖< M by unfold M; linarith)))
  refine ⟨M/(Nat.factorial (i+1):ℝ),by unfold M; positivity,?_⟩
  have hv : Tendsto (fun t:ℝ=> ((0:V),t*z)) (𝓝[>] 0) (𝓝 0):= by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds; simpa using! (show Continuous (fun t:ℝ=>((0:V),t*z)) by fun_prop).tendsto 0
  filter_upwards [eventually_pos,eventually_top hd,hv.eventually (h.eventually (by simp))] with t hT hk hF
  have hz : ContDiffAt ℝ ω (fun u:V=> F (u,t*z)) 0 := hF.comp (f:=fun u:V=>(u,t*z)) _ (contDiffAt_id.prodMk contDiffAt_const)
  have ha (r) (hy:r∈ uIcc 0 t) : ((t,r):ℝ×ℝ)∈ ball (0,0) d := by
    change r∈uIcc 0 t at hy; rw [uIcc_of_le hT.le] at hy
    change (t,r)∈ball (0:ℝ×ℝ) d; rw [mem_ball_zero_iff, Prod.norm_def, Real.norm_eq_abs, abs_of_pos hT,Real.norm_eq_abs,abs_of_nonneg hy.1,max_lt_iff]
    exact ⟨hk,hy.2.trans_lt hk⟩
  have hi : ContDiffOn ℝ ((i:WithTop ℕ∞)+1) (G t) (uIcc 0 t) := fun r hr=> ((show ContDiffAt ℝ ω _ _ from ((show ContDiffAt ℝ ω (uncurry G) (t,r) from (H (ha _ hr)).1).comp (f:=fun z:ℝ=> (t,z)) _ (contDiffAt_const.prodMk contDiffAt_id))).of_le le_top).contDiffWithinAt
  obtain ⟨r,hr,hR⟩:=taylor_mean_remainder_lagrange_iteratedDeriv (Ne.symm hT.ne') hi
  have hw: ‖P (t,r)‖ < M:= (H (ha r (Ioo_subset_Icc_self hr))).2
  rw [uIcc_of_le hT.le] at hR
  rw [Pi.sub_apply,show year (fun j t => jet (fun u:V => F (u,t*z)) j x) i t=taylorWithinEval (G t) i (Icc 0 t) 0 t from (plow i _ hz x hT).symm,show F (t•x,t*z)=G t t from rfl,hR,sub_zero,norm_div,norm_mul,Real.norm_eq_abs (_^_),abs_of_pos (pow_pos hT _),Real.norm_eq_abs ((Nat.factorial (i+1):ℝ)),abs_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  rw [div_mul_eq_mul_div]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hw.le (by positivity)) (by positivity)
end YM.RG08.Canon
