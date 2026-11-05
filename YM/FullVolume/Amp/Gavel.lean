import YM.FullVolume.Amp.Regain
/- uniformly. use compact from covers. Cauchy derivative Weierstrass mathlib. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Set RG Push.AbsoluteSums Ray Asymptotics
open scoped Topology BigOperators Classical ContDiff
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X] [NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y][NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y]
namespace Beam
variable (f:X→L[ℝ] Y) (x: Beam X) {r:ℝ}{z:ℂ}{C:ℝ}{P:ℕ→ Beam X}
omit [CompleteSpace Y] [NormedSpace ℂ Y] [IsScalarTower ℝ ℂ Y] in
private lemma still (hr:0≤r)(h:r ≤ 1)(Z:Beam X): Summable (fun i=> r^i*‖f (Z i)‖):=by
    have hs:Summable (fun i=> ‖f‖*‖Z i‖):= (paid Z).summable.mul_left _
    apply Summable.of_nonneg_of_le (fun _=>mul_nonneg (by positivity) (norm_nonneg _)) _ hs; intro i; apply (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr h)).trans; exact f.le_opNorm _
variable (hr:0<r)(ht:r<1)(hx: ‖x‖ ≤C)(hp:∀ i, ‖P i‖ ≤ C)(he:∀ i,Tendsto (fun n=> P n i) atTop (𝓝 (x i)))
include hx hp he
lemma bang (r:ℝ)(hr:0<r)(ht:r<1): TendstoUniformlyOn (fun n=>shine f (P n)) (shine f x) atTop (Metric.closedBall 0 r):=by
    let g(n i:ℕ):=r^i*‖f (x i)-f (P n i)‖
    have hg n (z:ℂ)(hz:‖z‖≤r): ‖shine f x z-shine f (P n) z‖≤ ∑' i,g n i:= by
       let u (Z:Beam X)(i:ℕ):= z^i • f (Z i)
       have hh (Z:Beam X): Summable (fun i=>‖u Z i‖):=by simp_rw [u,norm_smul,Complex.norm_pow]; exact still f (norm_nonneg _) (hz.trans ht.le) Z
       have hP i: u x i-u (P n) i=u (x-P n) i:=by unfold u; rw [← smul_sub,show f ((x-P n) i)=f (x i)-f (P n i) from map_sub f (x i) (P n i)]
       have hX: Summable (fun i=> ‖u x i-u (P n) i‖):=by simp_rw [hP]; exact hh _
       have hv: Summable (g n):= (still f hr.le ht.le (x-P n)).congr (fun i=> by unfold g; rw [← show f ((x-P n) i)=f (x i)-f (P n i) from map_sub f (x i) (P n i)])
       rw [shine,shine]; change ‖(∑' i,u x i)-∑' i,u (P n) i‖ ≤ _; rw [← Summable.tsum_sub (hh _|>.of_norm) (hh _|>.of_norm)]; apply (norm_tsum_le_tsum_norm hX).trans; exact hX.tsum_le_tsum (fun i=>by unfold u; rw [←smul_sub,norm_smul,norm_pow];exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hz _) (norm_nonneg _)) hv
    let t i :=r^(i:ℕ)*(‖f‖*C+‖f‖*C)
    have ha:Tendsto (fun i=> ∑' k,g i k) atTop (𝓝 0):= by
       have hh (X:Beam X)(hp:‖X‖ ≤ C)(i:ℕ): ‖f (X i)‖ ≤ ‖f‖*C:= (f.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((budget_single (togg X) i).trans hp) (norm_nonneg _))
       have he i: Tendsto (fun n=>g n i) atTop (𝓝 0) :=by unfold g; simpa only [sub_self,Function.comp_def,norm_zero,mul_zero] using (((f.continuous.continuousAt.tendsto.comp (he i)).const_sub (f (x i))).norm.const_mul (r^i))
       simpa only [tsum_zero] using (tendsto_tsum_of_dominated_convergence (bound:=t) ((summable_geometric_of_lt_one hr.le ht).mul_right (‖f‖*C+‖f‖*C)) he (Eventually.of_forall fun n i=>by rw [Real.norm_of_nonneg (show 0≤g n i by unfold g; positivity)]; exact mul_le_mul_of_nonneg_left ((norm_sub_le ..).trans (add_le_add (hh x hx i) (hh (P n) (hp n) i))) (pow_nonneg hr.le _)))
    refine Metric.tendstoUniformlyOn_iff.mpr fun ε hv=> (ha.eventually (gt_mem_nhds hv)).mono fun i hi z hz=>?_ ; rw [dist_eq_norm]; exact lt_of_le_of_lt (hg i z (mem_closedBall_zero_iff.mp hz)) hi
local notation "D"=> Metric.ball (0:ℂ) 1
lemma arrayP : TendstoLocallyUniformlyOn (fun n=>shine f (P n)) (shine f x) atTop D:=by
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mpr (fun K hk ht=>?_); rcases K.eq_empty_or_nonempty with h|h
    · subst K; exact (bang f x hx hp he (1/2) (by norm_num) (by norm_num)).mono (by simp)
    obtain ⟨z,hz,H⟩:= ht.exists_isMaxOn h continuous_norm.continuousOn; obtain ⟨r,h,h'⟩:= exists_between (mem_ball_zero_iff.mp (hk hz)); exact (bang f x hx hp he r (lt_of_le_of_lt (norm_nonneg _) h) h').mono fun z hz=> mem_closedBall_zero_iff.mpr ((H hz).trans h.le)
lemma version (i:ℕ) : TendstoLocallyUniformlyOn (fun n=>iteratedDeriv i (shine f (P n))) (iteratedDeriv i (shine f x)) atTop D:=by
    have hh i:∀ T:Beam X, AnalyticOnNhd ℂ (iteratedDeriv i (shine f T)) D:=by
        induction i with
        | zero=> intro T; rw [iteratedDeriv_zero]; exact fun z hz=> Amp.hol f T z (mem_ball_zero_iff.mp hz)
        | succ i ih=>intro T; rw [iteratedDeriv_succ]; exact fun z hz=> (ih T z hz).deriv
    induction i with
    | zero=> simpa using arrayP f x hx hp he
    | succ i ih=>simp_rw [iteratedDeriv_succ]; exact ih.deriv (Eventually.of_forall fun n=> (hh i (P n)).differentiableOn) Metric.isOpen_ball
end Beam
end YM.FullVolume.Amp
