import YM.RG08.Fold.Grads

/-! # Completed square staking from a true real quadratic germ on centered coords,
   any regulator; don't require analytic gauge family in g. -/
set_option autoImplicit false
noncomputable section
 set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
namespace YM.RG08.Fold
open Glyph Room Carrel Camera Matrix MvPolynomial Function Finset Filter
open scoped BigOperators ContDiff Topology Classical Matrix PowerSeries
variable {I O J B:Type}[Fintype I][Fintype J][Fintype O][Fintype B]
variable {A:Camera.Strip (Camera.Raw I B) (Camera.Raw I O)}
def tip (A:Camera.Strip I J):Matrix I J ℝ:=Matrix.of fun i j=>wedge j (A i) 0
def peek (p:Camera.Strip (Raw I B) (Raw I O)):Matrix I I ℝ:= (tip p).submatrix Sum.inl Sum.inl
def exof (p:Camera.Strip (Raw I B) (Raw I O)):Matrix I O ℝ:= (tip p).submatrix Sum.inl Sum.inr
def horn (p:Camera.Strip (Raw I B) (Raw I O)):Matrix B O ℝ:= (tip p).submatrix Sum.inr Sum.inr
abbrev silent (p:Camera.Strip (Raw I B) (Raw I O)):Prop:=∀ (i:B)(k:I),wedge (Sum.inl k) (p (.inr i)) =ᶠ[𝓝 0] (0: Still (Raw I O))

lemma intro_tip (A:Camera.Strip I J)(i:I): tap 0 (rescaleFields A i)=median (tip A) i:=by
 rw [rescaleFields,look,flute]; unfold print; simp only [Nat.cast_zero,zero_add,inv_one,one_smul]
 apply Finset.sum_congr rfl; intro k _; rw [Algebra.smul_def,mul_comm];rfl
private lemma med_read (L:Matrix I J ℝ)(i:I)(x:Cellar J): MvPolynomial.eval x (median L i)=(L *ᵥ x) i :=by simp only [median,map_sum,MvPolynomial.smul_eq_C_mul,eval_mul,eval_C,eval_X];rfl

lemma leadview (A:Camera.Strip I J)(p:Inn I)(x:Cellar J):
 MvPolynomial.eval x (tap 0 (belt (rescaleFields A) (liftInn p))) = MvPolynomial.eval (tip A *ᵥ x) p:=by
 rw [rim, tap,PowerSeries.coeff_C, if_pos rfl] -- name
 induction p using MvPolynomial.induction_on with
 | C=>simp
 | add _ _ ht hi=>rw [map_add,map_add,map_add,ht,hi]
 | mul_X a i h=>rw [_root_.map_mul,_root_.map_mul,_root_.map_mul,h,aeval_X,intro_tip,med_read,eval_X]

def acclim (A:Camera.Strip (Raw I B) (Raw I O)) (P Q:Matrix I I ℝ)(N:Matrix O O ℝ)(K:Matrix B B ℝ):Prop:=∀ x:Cellar I,∀ y:Cellar O, winery P x+winery N y= winery Q (peek A *ᵥ x+ exof A *ᵥ y) + winery K (horn A *ᵥ y)
lemma tipblocks (h:silent A)(x:Cellar (Raw I O))(i:I)(j:B):((tip A)*ᵥ x) (Sum.inl i) = ((peek A *ᵥ (x ∘ Sum.inl) + exof A *ᵥ (x ∘ Sum.inr)) i) ∧
     ((tip A)*ᵥ x) (Sum.inr j)=((horn A *ᵥ (x ∘ Sum.inr)) j):=by
 simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type];constructor; rfl
 simp only [tip,Matrix.of_apply,(h j _).self_of_nhds,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add];rfl
-- may be empty, separate
lemma tipread (h:silent A)(x:Cellar (Raw I O)) : ((tip A)*ᵥ x) ∘ Sum.inl = peek A *ᵥ (x ∘ Sum.inl) + exof A *ᵥ (x ∘ Sum.inr) ∧
     ((tip A)*ᵥ x) ∘ Sum.inr=horn A *ᵥ (x ∘ Sum.inr):=by
 constructor
 · ext i; simp only [Function.comp_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type];rfl
 ext i; simp only [Function.comp_apply,Matrix.mulVec,dotProduct,Fintype.sum_sum_type];simp only [tip,Matrix.of_apply,(h i _).self_of_nhds,Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add];rfl

private lemma winlift (P:Matrix I I ℝ)(N:Matrix B B ℝ)(x:Cellar (Raw I B)):
 MvPolynomial.eval x (heater P B + sink N I)=winery P (x ∘ Sum.inl)+winery N (x ∘ Sum.inr):=by rw [map_add,heater,sink,shelter_read,shelter_read]; simp_rw [eval_X,comp_def]

lemma acclimatize (h:silent A){P Q:Matrix I I ℝ}{N:Matrix O O ℝ}{K:Matrix B B ℝ}
   (p q : Port (Camera.Raw I O)) (v : Port (Camera.Raw I B)) -- classical exponents divided by g^2, after labels; no c=0 requirement
   (hp:tap 0 p=heater P O + sink N I)(hv:tap 0 v=heater Q B + sink K I)(hq:p=belt (rescaleFields A) v):acclim A P Q N K:=by
 have he : heater P O+sink N I=tap 0 (belt (rescaleFields A) (liftInn (heater Q B+ sink K I))):=by rw [←hp,hq,rim,hv,rim,tap,PowerSeries.coeff_C, if_pos rfl]
 intro x y
 let z:= (Sum.elim x y:Cellar (Raw I O))
 have hz: z ∘ Sum.inl=x:=rfl;have ht:z ∘ Sum.inr=y:=rfl
 rw [←hz,←ht,← winlift, he,leadview,winlift,(tipread h z).1,(tipread h z).2]

end YM.RG08.Fold
