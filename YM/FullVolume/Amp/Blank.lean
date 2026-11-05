import YM.FullVolume.Amp.Head
import Mathlib.Topology.Algebra.Module.Multilinear.Topology
/-! labeled polynomials along seminormed real dense legs. no completeness of X. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Amp
open Filter Function Finset Asymptotics Ray RG Push.AbsoluteSums
open scoped Topology BigOperators NNReal ENNReal ContDiff
variable {X Y I : Type*} [SeminormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y] [NormedAddCommGroup I][NormedSpace ℝ I]
variable {f:X→Y}{x:X}{c p r k:ℝ}{n j:ℕ}
-- extension induction: map all inputs step succ, use functor. uniform linear
section cap
variable (e:X →L[ℝ] I)(he:Isometry e)(h:DenseRange e)
include he h
lemma liftB (a:X→L[ℝ] Y): ‖a.extend e‖≤‖a‖:= ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (isClosed_property h (isClosed_le ((a.extend e).cont.norm) (by fun_prop)) fun x=>by rw [a.extend_eq h he.isUniformInducing,he.norm_map_of_map_zero (map_zero _)]; exact a.le_opNorm _)
lemma give (n:ℕ):∃ (P:(X[×n]→L[ℝ] Y) →L[ℝ] (I[×n]→L[ℝ] Y)), (∀ k,‖P k‖≤‖k‖)∧∀ k (u:Fin n→X),P k (fun i=>e (u i))=k u:=by
  induction n with
  | zero=>
     let P:(X[×0]→L[ℝ] Y) →ₗ[ℝ] (I[×0]→L[ℝ] Y):={ toFun := fun k=> ContinuousMultilinearMap.constOfIsEmpty ℝ _ (k 0), map_add' := fun x y=> by ext; rfl , map_smul' := fun x y=> by ext; rfl }
     have hh k:‖P k‖≤‖k‖:=by change ‖ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _:Fin 0=> I) (k 0)‖≤_; rw [ContinuousMultilinearMap.norm_constOfIsEmpty]; simpa using k.le_opNorm 0
     refine ⟨P.mkContinuous 1 (fun k=>by rw [one_mul]; exact hh k), hh,fun k u=>?_⟩
     exact congr_arg k (Subsingleton.elim 0 u)
  | succ n ih=>
    obtain ⟨P,hP,h₀⟩:= ih
    let y := I[×n]→L[ℝ] Y
    have ht (k:X[×(n+1)]→L[ℝ] Y) x u: ‖k (Fin.cons x u)‖≤‖k‖*‖x‖*∏ i, ‖u i‖:=by simpa only [Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_assoc] using k.le_opNorm (Fin.cons x u)
    let W(k:X[×(n+1)]→L[ℝ] Y) := MultilinearMap.mkContinuousLinear k.toMultilinearMap.curryLeft ‖k‖ (ht k)
    let Q(k:X[×(n+1)]→L[ℝ] Y): I[×(n+1)]→L[ℝ] Y:= ((P.comp (W k)).extend e).uncurryLeft
    have hv k (u:Fin (n+1)→X): Q k (fun i=>e (u i))=k u:=by
       unfold Q; rw [ContinuousLinearMap.uncurryLeft_apply, ContinuousLinearMap.extend_eq _ h he.isUniformInducing, ContinuousLinearMap.comp_apply]; change P _ (fun i=>e (Fin.tail u i))=k u; rw [h₀]; change k (Fin.cons (u 0) (Fin.tail u))=_; simp
    have hz k: ‖Q k‖≤‖k‖:=by
       unfold Q; rw [ContinuousLinearMap.uncurryLeft_norm]; apply (liftB e he h _).trans; refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
       intro x; rw [ContinuousLinearMap.comp_apply]; exact (hP _).trans (by apply ContinuousLinearMap.le_of_opNorm_le; exact MultilinearMap.mkContinuousLinear_norm_le _ (norm_nonneg _) _)
    have hi : DenseRange (fun u:Fin (n+1)→X=>fun i=> e (u i)):= DenseRange.piMap fun _=> h
    let V:(X[×(n+1)]→L[ℝ] Y) →ₗ[ℝ] (I[×(n+1)]→L[ℝ] Y):={
      toFun:=Q
      map_add':=fun x y=>by ext w; change Q (x+y) w=Q x w+Q y w; apply isClosed_property hi (isClosed_eq ((Q _).cont) ((Q x).cont.add (Q y).cont)) _ w; intro u; change Q (x+y) _=Q x _+Q y _; rw [hv,hv,hv]; try rfl
      map_smul':=fun x y=>by ext w; change Q (x • y) w=x • Q y w; apply isClosed_property hi (isClosed_eq ((Q _).cont) (continuous_const.smul (Q y).cont)) _ w; intro u; change Q (x • y) _=x • Q y _; rw [hv,hv]; try rfl }
    exact ⟨V.mkContinuous 1 (fun u=>by rw [one_mul]; exact hz u),hz,hv⟩ -- one_mul mismatch
variable (L: Often p f x r c)
include L
lemma stage : ∃ (P:FormalMultilinearSeries ℝ I Y), (∀ n, ‖P n‖ ≤ fee p r^n*c) ∧ ∀ z,‖z‖≤r → HasSum (fun n=> P n (fun _=> e z)) (f (x+z)) := by
   choose P hP h using fun n:ℕ=> give (Y:=Y) e he h n; exact ⟨fun n=>P n (L.gardenL n),fun n=> (hP ..).trans (L.course n),fun z hz=> (L.party _ hz).congr_fun (fun n=>h n _ (fun _=>z))⟩
end cap
end YM.FullVolume.Amp
