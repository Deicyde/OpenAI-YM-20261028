import YM.FullVolume.Amp.Gold
import Mathlib.Analysis.Complex.LocallyUniformLimit
/- Perturbed hol.UV using real Beam convergence. At s∈ interiors. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp.Beam
open Filter Function Finset Set RG Push.AbsoluteSums Ray
open scoped Topology BigOperators Classical ContDiff
variable {X Y:Type}[NormedAddCommGroup X][NormedSpace ℝ X][CompleteSpace X]
private lemma newest {ι:Type}[NormedAddCommGroup ι][CompleteSpace ι]{f:ℕ→ι}(h:∀ ε>0, ∃ g:ℕ→ι, (∀ n,‖g n-f n‖ ≤ ε)∧∃ M,Tendsto g atTop (𝓝 M)):∃ x,Tendsto f atTop (𝓝 x):=by
   refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr fun ε hp=>?_); obtain ⟨g,hg,M,hM⟩:= h (ε/4) (by positivity); obtain ⟨N,hN⟩:= Metric.cauchySeq_iff.mp hM.cauchySeq (ε/4) (by positivity); refine ⟨N,fun a ha b hb=>?_⟩
   have he i: dist (f i) (g i)≤ε/4 := by rw [dist_comm,dist_eq_norm]; exact hg i
   apply lt_of_le_of_lt (dist_triangle4 _ (g a) (g b) _); linarith [he a, he b,hN a ha b hb,dist_comm (f b) (g b)]
private def listens (P:Beam X)(m:ℕ)(z:ℝ):=∑ n∈Finset.range m,z^n • P n
variable {P:ℕ→ Beam X} {C:ℝ}
lemma album (T:Beam X)(m:ℕ)(x:sun)(hx:0<x.val): ‖read X x T-listens T m x.val‖ ≤ x.val^m*‖T‖:=by
   let f(k:ℕ):=x.val^k • T k; have hv:x.val ≤ 1:= x.property.2
   have hb: ‖T.arc x.val- listens T m x.val‖=‖∑' k,f (k+m)‖:=by rw [arc,← Summable.sum_add_tsum_nat_add m (T.spar (abs_le.mpr x.property)).summable]; unfold listens; dsimp only [f]; abel_nf; simp [add_comm m]
   change ‖T.arc x.val-_‖ ≤ _; rw [hb]
   have he: SumBudget (fun k=> ‖T (k+m)‖) ‖T‖:= budget_pull (·+m) (fun _ _=>Nat.add_right_cancel) (togg T)
   have hk : SumBudget (fun k=> ‖f (k+m)‖) (x.val^m*‖T‖):= budget_mono (budget_scale (pow_nonneg hx.le _) he) (fun k=>norm_nonneg _) fun k=> by
      unfold f; rw [norm_smul,pow_add,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (by positivity) (pow_le_one₀ hx.le hv)) (norm_nonneg _)
   exact (norm_tsum_le_tsum_norm hk.2.1).trans hk.2.2
lemma single_reads (h:∀ i, ‖P i‖≤ C)(H:∀ x:sun,∃ j,Tendsto (fun i=>read X x (P i)) atTop (𝓝 j))(m:ℕ):∃ j,Tendsto (fun i=> P i m) atTop (𝓝 j):=by
   induction m using Nat.strong_induction_on with | h n ih=>
   refine newest fun ε he=>?_ ; have hb:= (norm_nonneg _).trans (h 0)
   let t:= min (ε/(1+C)) 1; have ht:0<t:= lt_min (div_pos he (by linarith)) zero_lt_one; let s:sun:=⟨t,⟨by linarith,min_le_right ..⟩⟩
   let g(i):=(t^n)⁻¹ • (read X s (P i)-listens (P i) n t); have hh:0<t^n:=pow_pos ht n
   refine ⟨g,fun i=>?_,?_⟩
   · have hp:= album (P i) (n+1) s ht; unfold listens at hp; rw [sum_range_succ] at hp
     have hx : g i-P i n= (t^n)⁻¹ • (read X s (P i)-(listens (P i) n t+t^n • P i n)):=by unfold g; rw [smul_sub,smul_sub,smul_add,inv_smul_smul₀ hh.ne']; abel
     rw [hx,norm_smul,norm_inv,Real.norm_of_nonneg hh.le,inv_mul_le_iff₀ hh]; apply hp.trans; change t^(n+1)*‖P i‖ ≤ _; rw [pow_succ,mul_assoc]; refine mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_left ((h i).trans ?_) ht.le).trans (?_ : t*(1+C) ≤ε)) hh.le; · linarith
     exact (le_div_iff₀ (by linarith : 0<1+C)).mp (min_le_left ..)
   choose! S hS using ih; obtain ⟨k,hk⟩:= H s
   exact ⟨_,(hk.sub (tendsto_finsetSum (Finset.range n) (f:=fun k i=> t^k • P i k) (a:=fun k=> t^k • S k) (fun k hi=>(hS k (Finset.mem_range.mp hi)).const_smul _))).const_smul _⟩
lemma issueR (h:∀ i, ‖P i‖ ≤ C)(he:∀ x:sun,∃ j,Tendsto (fun i=>read X x (P i)) atTop (𝓝 j)):∃ U:Beam X, ‖U‖≤C∧∀ m:ℕ,Tendsto (fun i=> P i m) atTop (𝓝 (U m)):=by
   choose x hx using single_reads h he
   have hz : SumBudget (fun i=> ‖x i‖) C:= budget_of_sum (fun i=> norm_nonneg _) fun j=>le_of_tendsto' (tendsto_finsetSum _ (fun i (_:i∈j)=>(hx i).norm)) fun i => (budget_sum (togg (P i)) _).trans (h i)
   let u:Beam X:= ⟨x,memℓp_gen (by simpa only [ENNReal.toReal_one,Real.rpow_one] using hz.2.1)⟩
   exact ⟨u,(paid u|>.tsum_eq.symm).trans_le hz.2.2,hx⟩
end YM.FullVolume.Amp.Beam
