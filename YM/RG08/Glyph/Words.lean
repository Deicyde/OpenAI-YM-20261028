import YM.RG08.Steam.Valves
import YM.RG08.Cloud.Arch

/-!
# Finite stencil symbol and polynomial facts. `parley` uses no rank factorial.
Each term stands for the word product, so permuting or averaging over permutations
leaves the symbol exact. Only symmetric tensors are differentiated in these formulas.
-/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type}{n:ℕ}

abbrev Inn (I:Type):=MvPolynomial I ℝ
def word (x:Tape n I):Inn I:=∏ i,X (x i)
variable [Fintype I]
def parley (F:Flake n I):Inn I:=∑ x:Tape n I,F x • word x

omit [Fintype I] in
lemma word_perm (x:Tape n I)(e:Equiv.Perm (Fin n)):word (x ∘ e)=word x:=by unfold word;exact Equiv.prod_comp e (fun j=>X (x j))
lemma parley_perm (F:Flake n I)(e:Equiv.Perm (Fin n)):parley (woven F e)=parley F:=by
 unfold parley; rw [← Equiv.sum_comp (twist e) fun x=>F x • word x]
 simp [woven,twist,word_perm] -- word_perm maybe ∀?

lemma parley_zero : parley (0:Flake n I)=0:=by simp [parley]
lemma parley_add (F G:Flake n I):parley (F+G)=parley F+parley G:=by simp [parley,add_smul,Finset.sum_add_distrib]
lemma parley_sum {J:Type}(s:Finset J)(f:J→Flake n I):parley (s.sum f)=∑i∈s,parley (f i):=by
 induction s using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty];exact parley_zero
 | insert a s hi ih=>simp [sum_insert hi,parley_add,ih]
lemma parley_smul (a:ℝ)(F:Flake n I):parley (a • F)=a • parley F:=by simp [parley,Finset.smul_sum,smul_smul]
lemma parley_clean (F:Flake n I):parley (bleach F)=parley F:=by
 rw [bleach,parley_smul,parley_sum];simp_rw [parley_perm]
 let s:ℕ:=Fintype.card (Equiv.Perm (Fin n));have hs:(s:ℝ)≠0:=by dsimp [s]; exact_mod_cast Fintype.card_ne_zero
 rw [sum_const,card_univ,←show s=Fintype.card (Equiv.Perm (Fin n)) from rfl,← Nat.cast_smul_eq_nsmul ℝ,smul_smul,inv_mul_cancel₀ hs,one_smul]

omit [Fintype I] in
lemma word_cons (i:I)(x:Tape n I):word (Fin.cons i x)=X i*word x:=by simp [word,Fin.prod_univ_succ]

lemma parley_cons (F:Flake (n+1) I):parley F=∑ i,X i * parley (fun x:Tape n I=>F (Fin.cons i x)):=by
 unfold parley
 rw [← (Fin.consEquiv (fun _:Fin (n+1)=>I)).sum_comp fun x=>F x • word x,Fintype.sum_prod_type];apply sum_congr rfl; intro i _
 rw [Finset.mul_sum];apply sum_congr rfl;intro j _
 change _ • word (Fin.cons i j)=_
 rw [word_cons,mul_smul_comm];rfl

omit [Fintype I] in
lemma sym_cons {F:Flake (n+1) I}(h:Forms.Sym F)(i:I): Forms.Sym (fun x:Tape n I=>F (Fin.cons i x)):=by
 intro e
 -- use Fin.cons equivalence extending permutation, explicit permutation
 let f (j:Fin (n+1)):Fin (n+1):=Fin.cases (0:Fin (n+1)) (fun k=>(e k).succ) j
 let g (j:Fin (n+1)):Fin (n+1):=Fin.cases (0:Fin (n+1)) (fun k=>(e.symm k).succ) j
 let d:Equiv.Perm (Fin (n+1)):= ⟨f,g,fun j=>Fin.cases (by simp [f,g]) (fun k=>by simp [f,g]) j,fun j=>Fin.cases (by simp [f,g]) (fun k=>by simp [f,g]) j⟩
 funext x
 have he:= congrFun (h d) (Fin.cons i x)
 change F (Fin.cons i (x ∘ e)) = F (Fin.cons i x)
 have hd : Fin.cons i (x ∘ e) = (Fin.cons i x) ∘ d := by
   funext j
   cases j using Fin.cases <;> rfl
 exact (congrArg F hd).trans he

omit [Fintype I] in
private lemma repeat_two {F:Flake (n+2) I}(h:Forms.Sym F)(i j:I)(x:Tape n I):F (Fin.cons i (Fin.cons j x))=F (Fin.cons j (Fin.cons i x)):=by
 have he:=congrFun (h (Equiv.swap 0 (1:Fin (n+2)))) (Fin.cons j (Fin.cons i x))
 rw [←he];unfold woven;congr 1;ext k
 cases k using Fin.cases with
 | zero => rw [Fin.cons_zero,comp_apply,Equiv.swap_apply_left];rfl
 | succ k=> cases k using Fin.cases with
   | zero=>
     rw [comp_apply,show (0:Fin (n+1)).succ=(1:Fin (n+2)) from rfl,Equiv.swap_apply_right];rfl
   | succ k=>
     have hh:k.succ.succ≠ (1:Fin (n+2)):=by change k.succ.succ≠(0:Fin (n+1)).succ; exact fun h => (Fin.succ_ne_zero _) (Fin.succ_injective _ h)
     rw [comp_apply,Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) hh]
     simp

theorem first (i:I)(n:ℕ){F:Flake (n+1) I}(h:Forms.Sym F):pderiv i (parley F)=(n+1:ℝ) • parley (fun x:Tape n I=>F (Fin.cons i x)):=by
 induction n with
 | zero =>
   rw [parley_cons,map_sum]
   simp only [parley,word,prod_of_isEmpty,map_sum,Derivation.map_smul,Derivation.map_one_eq_zero,smul_zero,Derivation.leibniz,smul_eq_mul,pderiv_X,Pi.single_apply,mul_ite,mul_zero,mul_one]
   simp [Inn] 
 | succ n ih =>
   rw [parley_cons,map_sum]
   simp_rw [Derivation.leibniz,smul_eq_mul,pderiv_X,Pi.single_apply,mul_ite,mul_one,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq']
   simp only [Finset.mem_univ, if_true]
   have hd (j : I) :
       pderiv i (parley (fun x : Tape (n + 1) I => F (Fin.cons j x))) =
       (n + 1 : ℝ) • parley (fun x : Tape n I => F (Fin.cons i (Fin.cons j x))) := by
     rw [ih (sym_cons h j)]
     have hs : (fun x : Tape n I => F (Fin.cons j (Fin.cons i x))) =
         (fun x : Tape n I => F (Fin.cons i (Fin.cons j x))) :=
       funext (fun x => repeat_two h j i x)
     rw [hs]
   simp_rw [hd, mul_smul_comm]
   rw [← Finset.smul_sum,
     ← parley_cons (fun x : Tape (n + 1) I => F (Fin.cons i x))]
   simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]

end YM.RG08.Glyph
