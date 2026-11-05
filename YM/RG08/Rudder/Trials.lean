import Mathlib.Analysis.InnerProductSpace.l2Space
import YM.RG08.Forms.Coherent

/-!
# A simultaneous choice of lift: orthogonal calibration of any existence theorem
for a system of linear equations. No need for range of the operator to be closed. A
*difference with bounds* can require this; using an arbitrary lift twice isn't justified.
-/
noncomputable section
namespace YM.RG08.Rudder
open scoped Topology BigOperators Classical
set_option autoImplicit false
variable {I E X:Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][CompleteSpace E]
variable [TopologicalSpace X][AddCommGroup X][Module ℝ X] [T2Space X]

namespace Trial

/-- clm into test channels. -/
def dark (T:E→L[ℝ] X):= LinearMap.ker T.toLinearMap
omit [CompleteSpace E] in
lemma dark_closed (T:E→L[ℝ] X):IsClosed (dark T:Set E):= T.isClosed_ker
local instance (T:E→L[ℝ] X): CompleteSpace (dark T):= (dark_closed T).completeSpace_coe

def reflex (T:E→L[ℝ] X) : E →L[ℝ] E:= ContinuousLinearMap.id ℝ E - (dark T).starProjection

def reply (T:E→L[ℝ] X)(x:X):E:= if h:∃ a,T a=x then reflex T (Classical.choose h) else 0
lemma common (T:E→L[ℝ] X){a b:E}(h:T a=T b):reflex T a=reflex T b:=by
 rw [←sub_eq_zero,← map_sub];unfold reflex
 have he:a-b∈dark T:=show T (a-b)=0 by rw [map_sub,h,sub_self]
 simp [Submodule.starProjection_eq_self_iff.mpr he]
lemma reply_of (T:E→L[ℝ] X)(x:X){a:E}(h:T a=x):reply T x=reflex T a:=by
 let he:∃ a,T a=x:=⟨a,h⟩
 rw [reply,dif_pos he];exact common _ ((Classical.choose_spec he).trans h.symm)
lemma solves (T:E→L[ℝ] X)(x:X){a:E}(h:T a=x):T (reply T x)=x:=by
 rw [reply_of _ x h,reflex, sub_apply,ContinuousLinearMap.id_apply,map_sub]; have hv:(dark T).starProjection a∈dark T:=Submodule.starProjection_apply_mem ..
 change T ((dark T).starProjection a)=0 at hv;rw [h,hv,sub_zero]
theorem spend (T:E→L[ℝ] X)(x:X){a:E}(h:T a=x):‖reply T x‖≤ 2*‖a‖:=by
 rw [reply_of _ x h,reflex,sub_apply,ContinuousLinearMap.id_apply,two_mul];exact (norm_sub_le _ _).trans (add_le_add_right (Submodule.norm_starProjection_apply_le ..) _)
theorem subtract (T:E→L[ℝ] X){x y:X}(hx:∃ a,T a=x)(hy:∃ b,T b=y):reply T (x-y)=reply T x-reply T y:=by
 obtain ⟨a,rfl⟩:=hx;obtain ⟨b,rfl⟩:=hy
 simp_rw [reply_of T (a:=a) _ rfl,reply_of T (a:=b) _ rfl,←map_sub,reply_of T (a:=a-b) _ rfl] -- too many rewrites?
end Trial
end YM.RG08.Rudder
