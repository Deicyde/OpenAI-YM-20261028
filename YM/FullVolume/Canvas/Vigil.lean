import YM.FullVolume.Canvas.Radiance
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
/-! Weak sequences in CUT. Via testing actual ℓ². -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Tralis
open Filter Function Set lp
open scoped Topology BigOperators InnerProductSpace ContDiff NNReal ENNReal
abbrev Lights (J:Type) := lp (fun _:J=>ℝ) 2
variable {ι:Type}
structure Gleam (f:ℕ→Lights ι)(F:Lights ι) (b:ℝ): Prop where
    budget: ∀ᶠ i in atTop, ‖f i‖≤ b
    hinge:∀ x:ι,Tendsto (fun i=> f i x) atTop (𝓝 (F x))
lemma squaresP (f: Lights ι) : HasSum (fun i=>‖f i‖^2) (‖f‖^2):=by
   have he : 0 < (2:ℝ≥0∞).toReal:=by norm_num
   have hu := (memℓp_gen_iff he).mp (lp.memℓp f); have hx : HasSum (fun i=> ‖f i‖^(2:ℝ≥0∞).toReal) (‖f‖^(2:ℝ≥0∞).toReal):=by rw [lp.norm_rpow_eq_tsum he f]; exact hu.hasSum
   simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using hx
lemma flashes (f:ι→ℝ){b:ℝ}(h:∀ S:Finset ι, ∑ i∈S,‖f i‖^2 ≤b^2)(hp:0≤b): ∃ g:Lights ι,(∀ i,g i=f i)∧ ‖g‖≤ b:=by
    have he : Summable fun i=>‖f i‖^2 := summable_of_sum_le (fun i=>sq_nonneg _) h
    have hu : Memℓp (E:=fun _:ι=>ℝ) f 2:=memℓp_gen (by simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using he)
    let g:Lights ι:=⟨f,hu⟩
    have hx := (squaresP g)
    have hm : ‖g‖^2 ≤ b^2:= hx.tsum_eq.symm.trans_le (Real.tsum_le_of_sum_le (fun i=>sq_nonneg ‖f i‖) h)
    exact ⟨g,fun _=>rfl,by nlinarith⟩
lemma promos {f:ℕ→Lights ι} {b:ℝ}(h:∀ᶠ i in atTop,‖f i‖≤ b){g:ι→ℝ}(hp:∀ i,Tendsto (fun j=> f j i) atTop (𝓝 (g i))):∃ F: Lights ι,(∀ x,F x=g x)∧ ‖F‖≤ b∧ Gleam f F b:=by
    obtain ⟨F,he,hb⟩:= flashes g (b:=b) (fun S=> le_of_tendsto (tendsto_finsetSum _ fun i _=> (hp i).norm.pow 2) (h.mono fun i hx=>(((squaresP (f i)).summable.sum_le_tsum S (fun i _=>sq_nonneg _)).trans_eq (squaresP _).tsum_eq).trans (pow_le_pow_left₀ (norm_nonneg _) hx _))) (by obtain ⟨i,he⟩:=h.exists; exact (norm_nonneg _).trans he)
    exact ⟨F,he,hb,h,fun x=> (he x).symm ▸ hp x⟩
variable {F:Lights ι}{f:ℕ→ Lights ι}{b:ℝ}
lemma priced [Countable ι](h:∀ᶠ i in atTop,‖f i‖≤ b):∃ (g:Lights ι)(w:ℕ→ℕ), StrictMono w ∧ Gleam (f∘w) g b :=by
   let S:= Metric.closedBall (0:ℝ) b
   obtain ⟨g,hp,w,hM,hx⟩:= (isCompact_univ_pi (fun _ :ι=> show IsCompact S from isCompact_closedBall ..)).tendsto_subseq' (x:=fun i x=>(f i) x) (h.mono fun i hi x _=> by
       change dist _ 0≤b; rw [dist_zero_right]; exact (lp.norm_apply_le_norm (by norm_num) _ _).trans hi).frequently
   obtain ⟨Q,hQ,_,h'⟩:= promos (f:=f ∘ w) (hM.tendsto_atTop.eventually h) (tendsto_pi_nhds.mp hx)
   exact ⟨Q,w,hM,h'⟩
namespace Gleam
variable (H:Gleam f F b)
include H
lemma weight : ‖F‖≤ b:=by
   obtain ⟨Q,hq,hv,_⟩:= promos H.budget H.hinge; rwa [show F=Q from Eq.symm ((lp.ext_iff).2 (funext hq))]
lemma testing (x:Lights ι): Tendsto (fun i=>⟪f i,x⟫_ℝ) atTop (𝓝 ⟪F,x⟫_ℝ):=by
   classical
   have H' := lp.hasSum_single (by norm_num: (2:ℝ≥0∞)≠⊤) x
   let g (S:Finset ι):=∑ i∈ S, lp.single 2 i (x i)
   have h : Tendsto g atTop (𝓝 x):=H'
   have hu S:Tendsto (fun i=> ⟪f i,g S⟫_ℝ) atTop (𝓝 ⟪F,g S⟫_ℝ):=by
       unfold g; simp_rw [inner_sum,lp.inner_single_right]; exact tendsto_finsetSum _ fun i _=> (H.hinge i).inner tendsto_const_nhds
   rw [Metric.tendsto_nhds]
   intro ε he
   have hh:Tendsto (fun i=>b*‖x-g i‖) atTop (𝓝 0):=by simpa using (((tendsto_const_nhds (x:=x)).sub h).norm.const_mul b)
   obtain ⟨S,hS⟩:= (hh.eventually (gt_mem_nhds (by linarith:0< ε/3))).exists
   filter_upwards [H.budget,Metric.tendsto_nhds.mp (hu S) _ (by linarith:0<ε/3)] with i hi ht
   have hm (Q:Lights ι)(h:‖Q‖≤b) : dist ⟪Q,x⟫_ℝ ⟪Q,g S⟫_ℝ ≤ b*‖x-g S‖:=by
       rw [dist_eq_norm,←inner_sub_right]; exact (norm_inner_le_norm (𝕜:=ℝ) ..).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
   exact (dist_triangle4 _ ⟪f i,g S⟫_ℝ ⟪F,g S⟫_ℝ _).trans_lt (by rw [dist_comm ⟪F,g S⟫_ℝ]; linarith [hm _ hi,hm _ H.weight])
lemma wake (v:Lights ι→L[ℝ] ℝ): Tendsto (fun i=> v (f i)) atTop (𝓝 (v F)):=by
    let B := (InnerProductSpace.toDual ℝ (Lights ι)).symm v
    have he x : ⟪x,B⟫_ℝ = v x := (real_inner_comm _ _).trans (show ⟪B,x⟫_ℝ = v x from InnerProductSpace.toDual_symm_apply)
    have ht:= H.testing B; simp_rw [he] at ht; exact ht
lemma vectors {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X](v:Lights ι→L[ℝ] X): Tendsto (v∘f) atTop (𝓝 (v F)):=by
    let S:= (Module.finBasis ℝ X).equivFun.toContinuousLinearEquiv
    have ht:Tendsto (fun i=> S (v (f i))) atTop (𝓝 (S (v F))):= tendsto_pi_nhds.mpr fun i=>H.wake ((ContinuousLinearMap.proj i).comp (S.toContinuousLinearMap.comp v))
    simpa only [comp_def,S.symm_apply_apply] using S.symm.continuousAt.tendsto.comp ht
end Gleam
end YM.Stationary.Tralis
