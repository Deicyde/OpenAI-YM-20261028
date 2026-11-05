import YM.RG08.Aggregate.Voice

/-!
# Applying finite-dimensional real Hessian germ equation to Rail. Matrix conventions.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fold
open Glyph Room Carrel Camera Matrix MvPolynomial Function Finset
open scoped BigOperators ContDiff Topology Classical Matrix PowerSeries
variable {I O J B:Type}[Fintype I][Fintype J][Fintype O][Fintype B]

/-- actual negative exponent (logs at flat) as polynomial homogeneous. -/
def shelter (P:Matrix I I ℝ)(x:I→Inn O):Inn O :=(-(1:ℝ)/2) • ∑ i,∑ j,P i j • (x i*x j)
abbrev winB (P:Matrix I I ℝ)(x y:I→ℝ):=dotProduct x (P *ᵥ y)
def winery (P:Matrix I I ℝ)(x:I→ℝ):ℝ :=(-(1:ℝ)/2)*winB P x x
lemma winery_turn (P:Matrix I I ℝ)(he:P.transpose=P)(x y:I→ℝ):winB P x y=winB P y x:=by simpa only [he] using dotProduct_transpose_mulVec P x y
lemma winery_all (P:Matrix I I ℝ)(he:P.transpose=P)(x y:I→ℝ):winery P (x+y)=winery P x + winery P y - winB P x y:=by
 unfold winery; simp only [winB,add_dotProduct,Matrix.mulVec_add,dotProduct_add];change _= _ - winB _ _ _; have ht:=winery_turn P he x y;unfold winB at *; linarith

omit [Fintype O] in
lemma shelter_read (P:Matrix I I ℝ)(x:I→Inn O)(p:O→ℝ): MvPolynomial.eval p (shelter P x)=winery P (fun i=> MvPolynomial.eval p (x i)):=by
 change MvPolynomial.aeval p (shelter P x)=_
 simp only [shelter, map_sum,_root_.map_smul,_root_.map_mul,winB,winery,Matrix.mulVec,dotProduct,smul_eq_mul, Finset.mul_sum] ;apply Finset.sum_congr rfl;intro i _;apply Finset.sum_congr rfl;intro j _;change -1/2*(P i j*(MvPolynomial.eval p (x i)*MvPolynomial.eval p (x j)))=_;ring

-- internal gets block-independent external powers via view

def heater (P:Matrix I I ℝ)(O:Type):Inn (Camera.Raw I O):=shelter P (fun i=> X (Sum.inl i))
def sink (N:Matrix O O ℝ)(I:Type):Inn (Camera.Raw I O):=shelter N (fun i=> X (Sum.inr i))

def platen (N:Matrix O O ℝ)(I:Type):Port (Camera.Raw I O):=liftInn (sink N I)
omit [Fintype I] in
lemma perimeter (N:Matrix O O ℝ)(i:I): pin (Sum.inl i) (platen N I)=0:=by
 rw [platen,pin_c]
 simp [sink,shelter,pderiv_X,Derivation.map_smul]

omit [Fintype O] in
lemma glow (P:Matrix I I ℝ)(h:Pᵀ=P)(i:I):pderiv (.inl i:Raw I O) (heater P O)=-(∑ j,P i j • X (Sum.inl j)):=by
 simp only [heater,shelter,Derivation.map_smul,map_sum,pderiv_mul,pderiv_X,Pi.single_apply,Sum.inl.injEq,ite_mul,one_mul,zero_mul,mul_ite,mul_one,mul_zero,smul_add,smul_ite,smul_zero,Finset.sum_add_distrib]
 rw [Finset.sum_comm (f:=fun a (b:I)=>if a=i then (P a b • X (Sum.inl b):Inn (Raw I O)) else 0)] -- correct
 simp only [sum_ite_eq',mem_univ, ↓reduceIte]
 have ht(j v:I):P j v=P v j:=(congrFun (congrFun h v) j)
 conv_lhs=>arg 2;enter [2,2,x]; rw [ht x i]
 module

lemma heat (P Γ:Matrix I I ℝ)(H:Pᵀ=P)(R:∀ i j,Γ i j=Γ j i)(h:P*Γ=1): (morn Γ R O).Boil (fun x y=> Sum.elim (fun i=> Sum.elim (fun j=>P i j) (fun _=>0) y) (fun _=>0) x) (heater P O):=by
 constructor
 · rintro (i|i) hi (j|j)
   · have hv:=congrFun (congrFun h i) j
     simpa only [morn,Sum.elim_inl,Finset.sum_map,Function.Embedding.coeFn_mk,Matrix.mul_apply,Matrix.one_apply,Sum.inl.injEq] using hv
   · simp [morn]
   all_goals exfalso; simp [morn] at hi
 rintro (i|i) hi
 · simp [morn,glow _ H i]
 exfalso; simp [morn] at hi

end YM.RG08.Fold
