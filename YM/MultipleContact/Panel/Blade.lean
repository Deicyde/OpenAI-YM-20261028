import YM.MultipleContact.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! Mixed test derivatives: symmetry and total-jet budget. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MultipleContact.Panel
open Set Function Filter MeasureTheory
open scoped ContDiff Classical BigOperators
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def blade (v:E)(f:E→ℂ)(x:E):ℂ:=fderiv ℝ f x v
lemma blade_smooth {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(v:E):ContDiff ℝ ∞ (blade v f):=(hf.fderiv_right (by simp)).clm_apply contDiff_const

def blades (L:List E)(f:E→ℂ):E→ℂ:=match L with |[]=>f | v :: t=>blade v (blades t f)
lemma blades_smooth {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(L:List E):ContDiff ℝ ∞ (blades L f):=by induction L with |nil=> exact hf | cons v _ IH=> exact blade_smooth IH _
lemma blades_join {f:E→ℂ}(L T:List E): blades (L++T) f=blades L (blades T f):=by induction L with |nil=>rfl |cons v s IH=> exact congr_arg (blade v) IH
lemma blades_eval {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(k:ℕ)(m:Fin k→E)(x:E): blades (List.ofFn m) f x=iteratedFDeriv ℝ k f x m:=by
     induction k generalizing x with
     |zero=>rfl
     |succ k IH=>
        rw [List.ofFn_succ]; change blade (m 0) (blades _ f) x =_; rw [blade,funext (IH (fun i=>m i.succ))]
        exact (DifferentiableAt.iteratedFDeriv_succ_apply_left' (hf.differentiable_iteratedFDeriv (by change (k:WithTop ℕ∞)<(↑(⊤:ℕ∞));exact_mod_cast (show (k:ℕ∞)<⊤ by simp)) x)).symm
lemma norm_blades {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(L:List E)(hv:∀v∈L,‖v‖≤1)(x:E): ‖blades L f x‖ ≤ ‖iteratedFDeriv ℝ L.length f x‖:=by
       let m:=L.get; have h:List.ofFn m=L:=List.ofFn_get L
       rw [← h,blades_eval hf,List.length_ofFn]
       exact (ContinuousMultilinearMap.le_opNorm ..).trans (mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun _ _=>norm_nonneg _) (fun i _=>hv _ (List.get_mem ..))))
private lemma blade_double {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(v w x:E):blade v (blade w f) x=fderiv ℝ (fderiv ℝ f) x v w:=by
       unfold blade
       rw [fderiv_clm_apply ((hf.fderiv_right (by simp)).differentiable (by simp : (∞:WithTop ℕ∞)≠0) x) (differentiableAt_const w)]
       simp
lemma blade_commute {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(v w:E): blade v (blade w f)=blade w (blade v f):=
     funext fun x=> (blade_double hf ..).trans (((hf.of_le (show (2:ℕ∞ω)≤∞ by change ((2:ℕ∞):WithTop ℕ∞) ≤ (↑(⊤:ℕ∞));exact WithTop.coe_le_coe.mpr le_top)).contDiffAt.isSymmSndFDerivAt (by simp) v w).trans (blade_double hf ..).symm)
lemma blades_pin {f:E→ℂ}(hf:ContDiff ℝ ∞ f)(L:List E)(v:E):blade v (blades L f)=blades L (blade v f):=by
      induction L with
      |nil=> rfl
      |cons w L IH=>change blade v (blade w (blades L f))=_;rw [blade_commute (blades_smooth hf L) v,IH]; rfl
lemma blades_add {f g:E→ℂ}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g)(L:List E): blades L (f+g) = blades L f + blades L g:=by
     induction L with
     |nil=>rfl
     |cons v T IH=> funext x;dsimp only [blades];rw [IH]; change blade v (_ + _) x=_; rw [blade, fderiv_add ((blades_smooth hf T).differentiable (by simp) x) ((blades_smooth hg T).differentiable (by simp) x)];rfl
lemma blades_sub {f g:E→ℂ}(hf:ContDiff ℝ ∞ f)(hg:ContDiff ℝ ∞ g)(L:List E): blades L (f-g) = blades L f - blades L g:=by
         induction L with
         |nil=>rfl
         |cons v T IH=>funext x;dsimp only [blades]; rw [IH]; change blade v (_ - _) x=_;rw [blade,fderiv_sub ((blades_smooth hf T).differentiable (by simp) x) ((blades_smooth hg T).differentiable (by simp) x)];rfl
lemma blades_smul (a:ℝ){f:E→ℂ}(hf:ContDiff ℝ ∞ f)(L:List E): blades L (a • f)=a • (blades L f):=by
     induction L with
     |nil=>rfl
     |cons v T IH=>funext x;dsimp only [blades];rw [IH];rw [blade,fderiv_const_smul ((blades_smooth hf T).differentiable (by simp) x)]; rfl
lemma blades_zero (L:List E):blades L (0:E→ℂ)=0:=by induction L with |nil=>rfl |cons v L IH=>funext x; rw [blades,IH,blade]; simp
lemma blades_sum {ι:Type*}(w:Finset ι) (g:ι→E→ℂ)(hg:∀i,ContDiff ℝ ∞ (g i))(L:List E) (x:E): blades L (fun y=>∑i∈w,g i y) x=∑i∈w,blades L (g i) x:=by
     induction w using Finset.cons_induction with
     |empty=> change blades L 0 x=0; rw [blades_zero]; rfl
     |cons a w hw IH=>
       rw [Finset.sum_cons]; conv_lhs => arg 2; ext; rw [Finset.sum_cons]
       have hf : ContDiff ℝ ∞ (fun y=>∑i∈w,g i y):=ContDiff.sum (fun i _=>hg i)
       change blades L (g a + (fun y=>∑i∈w,g i y)) x = _
       rw [blades_add (hg a) hf,Pi.add_apply,IH]
end YM.MultipleContact.Panel
