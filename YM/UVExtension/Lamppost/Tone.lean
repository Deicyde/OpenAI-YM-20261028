import YM.UVExtension.Lamppost.Luster
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open ConnectedActivityE6 ConnectedActivityE6.Blaze Set Filter Function Topology
open scoped BigOperators ContDiff Classical
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {v w d C t : ℝ} {j : ℕ}

lemma rises {f : E→ℝ} (h : Brush j v d f x) : Brush j v d (fun x=> (f x:ℂ)) x := by
  have hx:= h.report Complex.ofRealCLM (ContinuousLinearMap.opNorm_le_bound _ (by norm_num : (0:ℝ)≤1) (fun u=> by simp))
  rwa [one_mul] at hx
lemma scales {f : E→ℂ} (h : Brush j v d f x) (c:ℂ) : Brush j (‖c‖*v) d (fun i=>c*f i) x := by
  have he:= (Brush.certified (k:=j) (le_refl 0) c).paints h; rwa [zero_add] at he
lemma all_thread {ι:Type} (s : Finset ι) (f : ι→E→ℂ) (g h : ι→ℝ) (he : ∀ i∈s, Brush j (g i) (h i) (f i) x) :
    Brush j (∏ i∈s,g i) (∑ i∈s,h i) (fun v=> ∏ i∈s, f i v) x := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty]; simpa only [norm_one] using! Brush.certified (k:=j) (le_refl 0) (1:ℂ)
  | insert i s hi hs => simp_rw [Finset.prod_insert hi,Finset.sum_insert hi]
                        exact (he i (Finset.mem_insert_self ..)).paints (hs fun i hi=> he i (Finset.mem_insert_of_mem hi))

lemma shimmers {f : E→ℂ} (h : Brush j v d (fun i=> f i-f x) x) (p : Brush j w 1 Complex.exp 0) :
    Brush j (‖Complex.exp (f x)‖) ((1+j.factorial*w)*((1+v)*d)) (fun i=>Complex.exp (f i)) x := by
  have hv:= h.pine (g:=Complex.exp) (by simpa)
  have he:= (hv.exalt (by simp only [sub_self,Complex.exp_zero,norm_one,le_refl]))
  apply (scales he (Complex.exp (f x))).climb (mul_one _|>.le) le_rfl|>.shimmy
  exact Eventually.of_forall fun i=> by dsimp only; rw [← Complex.exp_add,add_sub_cancel]
lemma climaxes (j:ℕ):∃ C:ℝ,0<C∧ ∀ (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (x:E) (w d : ℝ) (f : E→ℂ),
    Brush j w d f x → w≤1 → Brush j (C*w) d (fun i=> Complex.exp (f i)-1) x := by
  obtain ⟨v,hv,hp⟩:= Brush.compact (k:=j) (f:=fun y:ℂ => Complex.exp y-1) (isCompact_closedBall 0 1)
    (fun i hi=>(contDiffAt_id (𝕜:=ℝ)).cexp.sub contDiffAt_const)
  refine ⟨2+j.factorial*v,by positivity,?_⟩
  intro E _ _ x w d f hf hw
  have hk : ‖f x‖ ≤ 1:= hf.bound.trans hw
  exact Brush.even hf (hp _ (mem_closedBall_zero_iff.mpr hk)) hw (by norm_num) ((Complex.norm_exp_sub_one_le hk).trans (mul_le_mul_of_nonneg_left hf.bound (by norm_num)))
end YM.UVExtension.Lamppost
