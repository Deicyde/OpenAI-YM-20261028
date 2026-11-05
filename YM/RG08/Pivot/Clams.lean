import YM.RG08.Pivot.Pew

/-! # Finite-position covariance on tensor slots. Keep two true (time!)
factorials; self contractions are not stationary means. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Pivot
open Function Filter Lattice Wilson RG Exterior Precision Next.Free
open Laurent Bloch Matrix Work.F08 Tree FreeResolvent Stationary Finset
open UVExt.Paths Drift Scores Loom Shade Quire Tall Vale Analysis
open scoped Topology BigOperators Classical
variable {A B Q I : Type}[Fintype A][DecidableEq A][Fintype B][DecidableEq B]
variable {r k n : ℕ}

abbrev CupA (A : Type) [Fintype A] (r:ℕ) := Tensor.T (A → ℝ) ℝ r
abbrev Cupboard (A:Type) [Fintype A] := (n:ℕ)→ CupA A n

def tug {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (X : Matrix A B ℝ) := X.mulVecLin.toContinuousLinearMap
def bur (P:Matrix A A ℝ) (F:CupA A (r+2)): CupA A r := (batting r) • ∑ i,∑ j, P i j • (((F.curryLeft (zpk i)).curryLeft (zpk j)))
lemma bur_eval (P:Matrix A A ℝ)(F:CupA A (r+2))(v:Fin r→ A→ℝ):
    bur P F v= (batting r)*∑ i,∑ j,P i j * F (Fin.cons (zpk i) (Fin.cons (zpk j) v)) := by simp only [bur,_root_.smul_apply,_root_.sum_apply]; rfl
lemma bur_sym (P:Matrix A A ℝ){F:CupA A (r+2)}(hp:Tensor.Sym F): Tensor.Sym (bur P F) := by
  intro v k; unfold bur; simp only [_root_.smul_apply,_root_.sum_apply]; congr 1
  exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> congr_arg (P i j • ·) (Tensor.freeze_sym _ (Tensor.freeze_sym _ hp _) _ v k)
lemma bur_lap (P:Matrix A A ℝ){F:CupA A (r+2)}(hp:Tensor.Sym F): lap P (Tensor.diagonal F)=Tensor.diagonal (bur P F) := by
  funext v; rw [lap,show Tensor.diagonal (bur P F) v= _ from bur_eval P F (fun _=>v)]
  simp_rw [DDfade _ _ F hp v]; unfold batting; push_cast
  simp_rw [Finset.mul_sum]; refine sum_congr rfl fun i _ => sum_congr rfl fun j _=> by ring
lemma bur_cust (P : Matrix A A ℝ)(t : ℝ)(U:CupA A (r+2)) : bur P (t•U)=t• bur P U := by
  ext1 v; rw [bur_eval,_root_.smul_apply,bur_eval]; simp only [_root_.smul_apply,smul_eq_mul,Finset.mul_sum]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=> by ring
lemma bur_more (P:Matrix A A ℝ)(U V:CupA A (r+2)): bur P (U+V)=bur P U+bur P V:= by
  ext1 v; rw [bur_eval,_root_.add_apply,bur_eval,bur_eval]; simp only [_root_.add_apply,_root_.mul_add,sum_add_distrib]
lemma bur_home (P:Matrix A A ℝ):bur P (0:CupA A (r+2))=0:= by ext1; simp [bur_eval]
lemma burs_pledge {U:I→CupA A (r+2)} (P:Matrix A A ℝ)(s:Finset I): bur P (∑ i∈s,U i)=∑ i∈s,bur P (U i) := by
  induction s using Finset.induction_on with
  | empty=>simp [bur_home]
  | insert i s hi ih=> rw [sum_insert hi,sum_insert hi,bur_more,ih]
lemma bur_change (P Q:Matrix A A ℝ)(V:CupA A (r+2)) : bur (P+Q) V=bur P V+bur Q V:= by
  ext1 v; rw [bur_eval,_root_.add_apply,bur_eval,bur_eval]
  simp only [Matrix.add_apply,add_mul,sum_add_distrib,_root_.mul_add]

-- tract coordinate image
def twistV (X: Matrix A B ℝ) (V:CupA A r) : CupA B r := V.compContinuousLinearMap (fun _=> tug X)
lemma twists (X: Matrix A B ℝ)(V:CupA A r)(x : Fin r→ B→ℝ): twistV X V x=V (fun i => X *ᵥ x i):=rfl
lemma turns_sym (X: Matrix A B ℝ){V:CupA A r}(hp:Tensor.Sym V): Tensor.Sym (twistV X V):=fun x t=> hp (fun i=> X *ᵥ x i) t
lemma twist_total (X: Matrix A B ℝ)(U V:CupA A r): twistV X (U+V)=twistV X U+twistV X V:=rfl -- maps maybe not defeq ext
lemma twist_cost (X: Matrix A B ℝ)(a:ℝ)(U:CupA A r): twistV X (a•U)=a • twistV X U:= by ext1; rfl
lemma twist_for (X: Matrix A B ℝ)(U:I→CupA A r)(s : Finset I): twistV X (∑ i∈s,U i)=∑ i∈s, twistV X (U i) := by
   induction s using Finset.induction_on with
   | empty=> rw [sum_empty,sum_empty]; ext1; rfl
   | insert i s hi h=> rw [sum_insert hi,twist_total,sum_insert hi,h]
-- contract two legs of F over transformed slots only
lemma bur_wander (X : Matrix A B ℝ) (P:Matrix B B ℝ)(V:CupA A (r+2))(v: Fin r→ A→ℝ):
    bur (X*P*Xᵀ) V v=(batting r)*∑ i,∑ j,P i j * V (Fin.cons (X *ᵥ zpk i) (Fin.cons (X *ᵥ zpk j) v)) := by
  let F:=fun i j:A→ℝ => V (Fin.cons i (Fin.cons j v))
  have hu (Y:A→ℝ): Y=∑ i:A,Y i • zpk i := by ext1 x; simp [zpk,Finset.sum_apply,Pi.single_apply,mul_ite]; -- goal
  have hv x (b:A→ℝ) : F x b=∑ i:A,b i*F x (zpk i):=calc
    _ = (V.curryLeft x).curryLeft (∑ i:A,b i • zpk i) v := by rw [← hu]; rfl
    _ = _ := by rw [_root_.map_sum,_root_.sum_apply]; simp_rw [_root_.map_smul]; rfl
  have h (a b:A→ℝ): F a b=∑ i,∑ j,a i * b j * F (zpk i) (zpk j) := by
    rw [show F a b=∑ i:A,a i*F (zpk i) b from (by
       change V.curryLeft a (Fin.cons b v)=_
       nth_rw 1 [hu a]; rw [_root_.map_sum,_root_.sum_apply]; simp_rw [_root_.map_smul]; rfl)]
    exact sum_congr rfl fun i _=> by rw [hv (zpk i) b,Finset.mul_sum]; exact sum_congr rfl fun j _=> by ring
  have hm i j : V (Fin.cons (X *ᵥ zpk i) (Fin.cons (X *ᵥ zpk j) v))=
      ∑ a,∑ b, X a i * X b j * V (Fin.cons (zpk a) (Fin.cons (zpk b) v)) := by
    simpa only [zpk,mulVec_single_one,col, Matrix.transpose_apply,F] using h (X *ᵥ zpk i) (X *ᵥ zpk j)
  simp_rw [hm,bur_eval,Matrix.mul_apply,Matrix.transpose_apply]; congr 1; simp_rw [Finset.sum_mul,Finset.mul_sum]
  let T a b i j := X a j*P j i*X b i * V (Fin.cons (zpk a) (Fin.cons (zpk b) v))
  have he : (∑ a:A,∑ b:A,∑ i:B,∑ j:B,T a b i j)=∑ j:B,∑ i:B,∑ a:A,∑ b:A,T a b i j := by
    have hh : (∑ a:A,∑ b:A,∑ i:B,∑ j:B,T a b i j)=(∑ a:A×A,∑ i:B×B,T a.1 a.2 i.2 i.1):=by
       simp_rw [Fintype.sum_prod_type]; exact sum_congr rfl fun a _=> sum_congr rfl fun b _ => Finset.sum_comm
    rw [hh, Finset.sum_comm]; simp_rw [Fintype.sum_prod_type]
  exact he.trans (sum_congr rfl fun j _=> sum_congr rfl fun i _=> sum_congr rfl fun a _=> sum_congr rfl fun b _=> by unfold T; ring)


lemma bur_turns (X : Matrix A B ℝ) (P: Matrix B B ℝ)(V:CupA A (r+2)) :
    bur P (twistV X V)=twistV X (bur (X*P*Xᵀ) V) := by
  ext1 v; rw [twists,bur_wander,bur_eval]; congr 1
  apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; apply congr_arg (P i j * ·); rw [twists]
  congr 1; funext x; refine Fin.cases ?_ (fun i=> ?_) x; · rfl
  simp only [Fin.cons_succ]; cases i using Fin.cases <;> rfl

end YM.RG08.Pivot
