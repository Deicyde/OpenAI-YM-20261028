import YM.RG08.Fold.Towers

/-!
# Scalar quadratic law ⇒ full transferred inverse covariance incl symmetry. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Fold
open Glyph Room Carrel Camera Matrix MvPolynomial Function Finset Filter
open scoped BigOperators ContDiff Topology Classical Matrix PowerSeries
variable {I O J B:Type}[Fintype I][Fintype J][Fintype O][Fintype B]
variable {A:Camera.Strip (Camera.Raw I B) (Camera.Raw I O)}
variable {P Q:Matrix I I ℝ} {N:Matrix O O ℝ}{K:Matrix B B ℝ}

lemma lean_in (H : acclim A P Q N K)(x:Cellar I):winery P x=winery Q (peek A *ᵥ x):=by
 have hh i : winery i (0:Cellar O)=0:=by simp [winery,winB]
 simpa [winery,winB] using H x 0

lemma lean_cash (H:acclim A P Q N K)(hQ:Qᵀ=Q)(hP:Pᵀ=P): P=(peek A)ᵀ*Q*peek A:=by
 let L:=peek A
 have hv(x y:Cellar I):winB P x y=winB Q (L *ᵥ x) (L *ᵥ y):=by
    have he:=lean_in H (x+y); rw [mulVec_add,winery_all _ hP,winery_all _ hQ,lean_in H x,lean_in H y] at he; linarith only [he]
 have ht(x y):winB ((L)ᵀ*Q*L) x y=winB Q (L *ᵥ x) (L *ᵥ y):=by
    unfold winB;rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_transpose_mulVec,dotProduct_comm]
 ext i j
 have he(V:Matrix I I ℝ): winB V (Pi.single i 1) (Pi.single j 1)=V i j:=by simp [winB,mulVec,dotProduct,Pi.single_apply,mul_ite,ite_mul,one_mul,mul_one]
 exact (he P).symm.trans ((hv _ _).trans ((ht _ _).symm.trans (he (Lᵀ * Q * L))))

lemma lean_out (H:acclim A P Q N K)(hQ:Qᵀ=Q)(h:IsUnit Q.det)(hh:IsUnit (peek A)): exof A=0:=by
 let S:=exof A; let L:=peek A
 have he (x:Cellar I)(y:Cellar O):winB Q (L*ᵥ x) (S*ᵥ y)=0:=by
    have ht:=H x y;rw [winery_all _ hQ,lean_in H x] at ht
    have hs:= H 0 y;rw [show winery P 0=0 from by simp [winery,winB],mulVec_zero,zero_add,zero_add] at hs
    simp only [hs] at ht
    unfold S L;linarith
 have hp :L*L⁻¹=1:=L.mul_nonsing_inv (L.isUnit_iff_isUnit_det.mp hh)
 have hv(y:Cellar O):S *ᵥ y=0:=by
    have hs(x:Cellar I):winB Q x (S*ᵥ y)=0:=by have hx:=he (L⁻¹*ᵥ x) y; rwa [mulVec_mulVec,hp,one_mulVec] at hx
    have Hq:Q *ᵥ (S *ᵥ y) = 0:=by
      ext i; exact (by simpa [winB,dotProduct,Pi.single_apply,ite_mul] using hs (Pi.single i 1))
    have hh':Q⁻¹ *ᵥ (Q *ᵥ (S*ᵥ y))=0:=by rw [Hq,mulVec_zero]
    rwa [mulVec_mulVec,Matrix.nonsing_inv_mul _ h,one_mulVec] at hh'
 ext i j
 have h:=congrFun (hv (Pi.single j 1)) i; change S i j=0; simpa [mulVec_single] using h

lemma lean_cov (H:acclim A P Q N K)(hQ:Qᵀ=Q)(hP:Pᵀ=P)(hp:IsUnit P.det)(hq:IsUnit Q.det)(hh:IsUnit (peek A)): peek A * P⁻¹ * (peek A)ᵀ=Q⁻¹:=by
 let L:= peek A
 have hv:Lᵀ * Q * L=P:=(lean_cash H hQ hP).symm
 have h1:L⁻¹*L=1:=L.nonsing_inv_mul (L.isUnit_iff_isUnit_det.mp hh)
 have h2:L*L⁻¹=1:=L.mul_nonsing_inv (L.isUnit_iff_isUnit_det.mp hh)
 have he: (L * P⁻¹ * Lᵀ)*Q=1:=by
    have hx:Lᵀ*Q=P*L⁻¹:=by rw [←hv,Matrix.mul_assoc,h2,Matrix.mul_one]
    rw [Matrix.mul_assoc,hx,←Matrix.mul_assoc,Matrix.mul_assoc L,Matrix.nonsing_inv_mul _ hp, Matrix.mul_one,h2]
 change L*P⁻¹*Lᵀ=_
 conv_lhs=> rw [← Matrix.mul_one (L*P⁻¹*Lᵀ),← Matrix.mul_nonsing_inv _ hq,←Matrix.mul_assoc,he,Matrix.one_mul]

-- connect directly to recommended inverse placeholders
lemma railize (H:acclim A P Q N K)(hL:IsUnit (peek A))(hq:Qᵀ=Q)(h:IsUnit Q.det)(hh:silent A)(hs:∀ i,Pace (A i))(hi:Camera.roll A 0=0): ∃ q: Rail I O B,q.h=A:=by
 refine ⟨⟨A,peek A,hL,hi,fun i j=>rfl,?_,hh,hs⟩,rfl⟩
 intro i j; exact congrFun (congrFun (lean_out H hq h hL) i) j

lemma peekID (q:Rail I O B):peek q.h=q.L:=by ext i j;exact q.leading i j

lemma firstRail (q:Rail I O B)(H:acclim q.h P Q N K):belt q.b (liftInn (heater Q B))=liftInn (heater P O):=by
 have hx(i:I):q.b (.inl i)= ∑ j:I,q.L i j • (rod (Sum.inl (β:=O) j)):=rfl
 rw [belt_c];unfold heater shelter; simp only [_root_.map_smul,map_sum,_root_.map_mul,lug,MvPolynomial.aeval_X,hx]
 -- push liftInn outside after proving polynomial eval equality
 let F(i:I):Inn (Raw I O):=∑ j:I,q.L i j • X (Sum.inl j)
 have h0(a:ℝ)(b:Inn (Raw I O)): a • liftInn b=liftInn (a • b):=by rw [Algebra.smul_def,Algebra.smul_def,_root_.map_mul,PowerSeries.algebraMap_apply]
 unfold rod;
 have hF(i:I):(∑ j:I,q.L i j • (liftInn (X (Sum.inl (β:=O) j)) :Port (Raw I O)))=liftInn (F i):=by simp_rw [h0,← map_sum];rfl
 simp_rw [hF,←_root_.map_mul,h0,←map_sum,h0]
 apply congrArg; apply MvPolynomial.funext;intro x
 change MvPolynomial.eval x (shelter Q F)=MvPolynomial.eval x (shelter P (fun i=>X (Sum.inl i)))
 rw [shelter_read,shelter_read,lean_in H (fun i=>_),peekID];congr 1;funext i;simp [F,mulVec,dotProduct,MvPolynomial.smul_eq_C_mul]
end YM.RG08.Fold
