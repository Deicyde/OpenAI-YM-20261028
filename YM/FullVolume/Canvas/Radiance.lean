import YM.Analysis.Symmetric
import YM.Next.STATIONARY.Infrastructure.Jets
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
/-! Any pointwise continuously linear supplied infinite data with *pointwise analytic germs* on configs automatically gives ContinuousLinear transform for finite jet by Banach-Steinhaus. Uniform domains not prerequisite. Real parameters on completed ℓ² only. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Tralis
open Filter Function Asymptotics Tensor
open scoped Topology ContDiff BigOperators
variable {E F X:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E]
  [NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F] [NormedAddCommGroup X][NormedSpace ℝ X]
variable {f:E→X→F}(h:∀ x: X,∃ S:E→L[ℝ] F,∀ i,S i=f i x)(hp:∀ e,AnalyticAt ℝ (f e) 0)
private lemma radiants {g : X→F} {p:FormalMultilinearSeries ℝ X F} (h:HasFPowerSeriesAt g p 0)(t:ℕ)(x:X):
    Tendsto (fun b:ℝ=> (b^t)⁻¹ • (g (b • x) - p.partialSum t (b • x))) cutRay (𝓝 (diagonal (p t) x)):=by
   apply scale_limit (f:=fun b:ℝ=>g (b • x)-p.partialSum t (b • x))
   have he := (h.isBigO_sub_partialSum_pow (t+1)).comp_tendsto (along x)
   simp only [Function.comp_def, zero_add,norm_smul] at he
   have hx := he.trans (isBigO_of_le' (g:=fun b:ℝ=>b^(t+1)) (c:=‖x‖^(t+1)) _ fun b => by rw [norm_pow,norm_pow, Real.norm_of_nonneg (by positivity), mul_pow, mul_comm])
   convert hx using 1
   ext b; rw [show p.partialSum (t+1) _=p.partialSum t _ + diagonal (p t) _ from Finset.sum_range_succ .., homogeneous]; abel
lemma principal (n:ℕ): ∃ h: Submodule ℝ (T X F n), ∀ H, H∈h↔Sym H:=by
    refine ⟨{carrier:={H|Sym H},zero_mem':=fun _ _=>rfl,add_mem':=?_, smul_mem':=?_},fun _=>Iff.rfl⟩
    · intro H E h he i p; simp only [_root_.add_apply]; rw [show H (i∘p)=_ from h ..,show E (i∘p)=_ from he ..]
    intro r H h i p; simp only [_root_.smul_apply]; rw [show H (i∘p)=_ from h ..]
private lemma bam {u:E→ₗ[ℝ] F}(q:ℕ→ E→L[ℝ] F)(h:∀ e,Tendsto (fun n=> q n e) atTop (𝓝 (u e))): Continuous u :=by
     obtain ⟨C,hC⟩ := banach_steinhaus (g:=q) (fun e=> by obtain ⟨C,hC⟩ := (h e).norm.bddAbove_range; exact ⟨C,Set.forall_mem_range.mp hC⟩)
     have ht e : ‖u e‖≤ C*‖e‖:= le_of_tendsto' (h e).norm fun n=> ((q n).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))
     exact (LinearMap.mkContinuous u C ht).continuous
open Set
variable [FiniteDimensional ℝ F][FiniteDimensional ℝ X]
include h hp
lemma starlight: ∀ n,∃ S:E→L[ℝ] T X F n,∀ e,S e= iteratedFDeriv ℝ n (f e) 0:=by
    classical
    intro n; induction n using Nat.strong_induction_on with
    | h n ih=>
     obtain ⟨P,hP⟩ := principal (X:=X) (F:=F) n
     let b (e:E) : P :=⟨_,(hP _).2 (coeff_symm (hp e |>.contDiffAt (n:=n) : ContDiffAt ℝ (n:ℕ) _ _))⟩
     let A:P→ₗ[ℝ](X→F):= {toFun:=fun e=> diagonal e.val,map_add':=fun _ _ => rfl,map_smul':=fun _ _=>rfl}
     have hv: Injective A:= fun x y h=>Subtype.ext (ext_diag _ _ ((hP _).1 x.2) ((hP _).1 y.2) h)
     have he:= LinearMap.isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.mpr hv)
     choose S hs using h
     choose! D hd using ih
     have hz x y : f (x+y)= f x+f y:=funext fun i=> by rw [←hs,Pi.add_apply,←hs,←hs,map_add]
     have hx (r:ℝ) x : f (r • x)= r • f x:=funext fun i=> by rw [←hs,Pi.smul_apply,←hs,map_smul]
     let M:E→ₗ[ℝ] P:= {toFun:= b,map_add':=fun x y=>Subtype.ext (by
                                                                    change coeff (f (x+y)) n 0= coeff (f x) n 0 + coeff (f y) n 0; rw [hz]; unfold coeff; rw [iteratedFDeriv_add_apply (hp x|>.contDiffAt) (hp y|>.contDiffAt),smul_add]),
                        map_smul':=fun r x=>Subtype.ext (by
                                change coeff (f (r • x)) n 0 = r • coeff (f x) n 0; unfold coeff; rw [hx,iteratedFDeriv_const_smul_apply (hp x |>.contDiffAt),smul_comm])}
     let W := fun e:E=> (M e).val
     have H (x:X): Continuous fun e:E=> diagonal (W e) x :=by
         let l (i:ℕ):=(1/2:ℝ)^i
         have hl : Tendsto l atTop cutRay := tendsto_nhdsWithin_iff.mpr ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:0≤(1/2:ℝ)) (by norm_num),Eventually.of_forall fun i=> pow_ne_zero _ (by norm_num: (1/2:ℝ)≠0)⟩
         let U:E→ₗ[ℝ] F:= (LinearMap.proj x).comp (A.comp M)
         let J (i m:ℕ):T X F m →L[ℝ] F:= ContinuousMultilinearMap.apply ℝ _ F (fun _=> l i • x)
         let Q i : E→L[ℝ] F:=(l i^n)⁻¹ • (S (l i • x) - ∑ j∈ Finset.range n, (j.factorial:ℝ)⁻¹ • ((J i j).comp (D j)))
         refine bam (u:=U) Q fun e=>?_
         obtain ⟨P',h'⟩:=hp e
         have hy m y:diagonal (coeff (f e) m 0) y = diagonal (P' m) y:=by
                 unfold Tensor.diagonal coeff; rw [_root_.smul_apply,show iteratedFDeriv ℝ m (f e) 0 (fun _=> y)= _ from diag_derivative h' m y, inv_smul_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))]; rfl
         change Tendsto _ _ (𝓝 (diagonal (coeff (f e) n 0) x)); rw [hy]
         refine ((radiants h' n x).comp hl).congr fun i=> ?_
         unfold Q; simp only [_root_.smul_apply,_root_.sub_apply,_root_.sum_apply, hs,ContinuousLinearMap.comp_apply,Function.comp_apply]; congr 2; refine Finset.sum_congr rfl fun j hm=>?_; rw [hd j (Finset.mem_range.mp hm)]; exact (hy j _).symm
     have hM:Continuous M := he.isEmbedding.isInducing.continuous_iff.mpr (continuous_pi H)
     let D : E →L[ℝ] P:=⟨M,hM⟩
     exact ⟨(n.factorial:ℝ) • P.subtypeL.comp D, fun x=> by
         change (n.factorial:ℝ) • ((n.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ n (f x) 0)) = _; exact smul_inv_smul₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) _⟩
end YM.Stationary.Tralis
