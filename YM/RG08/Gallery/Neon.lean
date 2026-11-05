import YM.RG08.Gallery.Signals

/-! # Discrete trace-off gradient Wick projection at arbitrary rank,
via polynomial in interpolation parameter (no estimates). -/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Gallery
open Forms Glyph Room Camera Finset Lattice Laurent Pert.Bulk Function MvPolynomial Filter Isles
open scoped Topology BigOperators ContDiff PowerSeries Classical
variable {I J:Type}{n:ℕ}

variable [Fintype I]

def letter (a b:I→ℝ)(i:I):MvPolynomial Unit ℝ:=C (a i)+C (b i)*X ()
lemma nib (a b:I→ℝ)(f:Inn I):pderiv () (MvPolynomial.aeval (letter a b) f)= ∑ i,b i • MvPolynomial.aeval (letter a b) (pderiv i f):=by
 let t:=MvPolynomial.aeval (letter a b) (R:=ℝ)
 change pderiv () (t f)=∑ i,b i • t (pderiv i f)
 induction f using MvPolynomial.induction_on with
 | C r=> unfold t; simp
 | add f g h H=>simp only [map_add,h,H,Finset.sum_add_distrib,smul_add]
 | mul_X f i h=>
   have he (i j:I): pderiv j (X (R:=ℝ) i)=if i=j then 1 else 0:=by simp [pderiv_X,Pi.single_apply]
   have hv (x:I): t (X x)=letter a b x:=MvPolynomial.aeval_X ..
   rw [map_mul,pderiv_mul,h,hv]; simp only [pderiv_mul,map_add,smul_add,sum_add_distrib]
   rw [Finset.sum_mul]; simp_rw [map_mul,hv,smul_mul_assoc, he]
   congr 1
   rw [Finset.sum_eq_single i]
   · simp only [letter,map_add,pderiv_mul,pderiv_X_self,pderiv_C,zero_mul,mul_one,zero_add,↓reduceIte,map_one];rw [Algebra.smul_def,mul_comm];rfl
   · intro l _ hl;rw [if_neg (Ne.symm hl),map_zero,mul_zero,smul_zero]
   simp

/-- if invariant under a fixed addition b, directional derivative vanishes as a
polynomial (first slot and every monomial choice for other slots). -/
lemma zap (b:I→ℝ)(f:Inn I)(h:∀ (temp:ℝ)(a:I→ℝ),MvPolynomial.eval (a+temp • b) f=MvPolynomial.eval a f) : (∑ i,b i • pderiv i f)=0:=by
 apply MvPolynomial.funext;intro a
 have he (x:Unit→ℝ)(f:Inn I): MvPolynomial.eval x (MvPolynomial.aeval (letter a b) f)=MvPolynomial.eval (a+x () • b) f:=by
    induction f using MvPolynomial.induction_on with
    | C r=>simp
    | add f g ih ih'=> simp only [map_add,ih,ih']
    | mul_X f i hi=> simp only [map_mul,MvPolynomial.aeval_X, letter,map_add,eval_X,eval_C,hi,Pi.add_apply,Pi.smul_apply,smul_eq_mul];ring
 have ht:MvPolynomial.aeval (letter a b) f=C (MvPolynomial.eval a f):=by apply MvPolynomial.funext;intro x;rw [he,eval_C,h]
 have hg: pderiv () (MvPolynomial.aeval (letter a b) f)=0:=by rw [ht,pderiv_C]
 rw [nib] at hg;apply_fun MvPolynomial.aeval (fun _:Unit=> (0:ℝ)) at hg
 simp only [map_sum,_root_.map_smul,smul_eq_mul,map_zero] at hg
 change (MvPolynomial.aeval a) _=(MvPolynomial.aeval a) _
 simp only [map_sum,_root_.map_smul,map_zero,smul_eq_mul]
 have hu(g:Inn I): MvPolynomial.aeval (fun _:Unit=> (0:ℝ)) (MvPolynomial.aeval (letter a b) g)=MvPolynomial.aeval a g:=by
    change (MvPolynomial.eval (fun _:Unit=> (0:ℝ)) _)=(MvPolynomial.eval a _)
    simp only [he,zero_smul,add_zero]
 simpa only [hu] using hg

lemma first_gap {F:Flake (n+1) I}(hf:Sym F)(b:I→ℝ)(hv:∀ (temp:ℝ)(a:I→ℝ),MvPolynomial.eval (a+temp • b) (parley F)=MvPolynomial.eval a (parley F))
    (w:Tape n I): (∑ i, b i * F (Fin.cons i w))=0:=by
 let T i:Flake n I:=fun v=>F (Fin.cons i v)
 have ht i:Sym (T i):=sym_cons hf _
 let V := ∑ i,b i • T i
 have he:=zap b (parley F) hv
 simp_rw [first _ _ hf] at he
 have hs: (n+1:ℝ) • parley V=0:=by unfold V;rw [parley_sum,Finset.smul_sum];simp_rw [parley_smul,smul_comm (n+1:ℝ)];exact he
 have H:parley V=parley (0:Flake n I):=by rw [parley_zero]; exact Cloud.untangle (by positivity:(n+1:ℝ)≠0) (by simpa using hs)
 have hm:=Carrel.pursuit (F:=V) (by intro e; ext x; unfold woven V; simp only [Finset.sum_apply,Pi.smul_apply]; simp_rw [show ∀ i,T i (x ∘ ⇑e)=T i x from fun i=>congrFun (ht i e) x]) Sym.zero H
 have hP:=congrFun hm w; unfold V T at hP;simpa only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] using hP

end YM.RG08.Gallery
