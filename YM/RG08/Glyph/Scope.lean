import YM.RG08.Glyph.Words

noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I] {p q n:ℕ}

abbrev axes (I:Type):Cloud.Gauge I (Inn I):=fun i=>MvPolynomial.pderiv i
def half (Γ : Line I):=fun i j=>Γ i j / 2

omit [Fintype I] in
lemma word_twine (x:Tape p I)(y:Tape q I):word (Fin.append x y)=word x * word y:=by
 unfold word; rw [←Equiv.prod_comp finSumFinEquiv fun i=>X ((Fin.append x y) i), Fintype.prod_sum_type];simp

private lemma parley_weld (Γ : Line I) (F : Flake (p+1) I) (G : Flake (q+1) I) : parley (weld Γ F G) =
      ∑ i,∑ j,Γ i j • (parley (fun x:Tape p I=>F (Fin.cons i x))*parley (fun y:Tape q I=>G (Fin.cons j y))):=by
 unfold weld; simp_rw [tsum_fintype]
 conv_lhs=> unfold parley
 
 simp_rw [Finset.sum_smul] -- fix
 rw [Finset.sum_comm,Fintype.sum_prod_type]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl;intro j _
 rw [← (Fin.appendEquiv p q).sum_comp (fun x=>seam Γ F G x (i,j) • word x),Fintype.sum_prod_type]
 unfold parley; rw [Finset.sum_mul,Finset.smul_sum]; apply Finset.sum_congr rfl; intro x _; rw [Finset.mul_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro y _
 change seam _ _ _ (Fin.append x y) _ • word (Fin.append x y)=_
 rw [seam_tool,word_twine, smul_mul_assoc,mul_smul_comm,smul_smul,smul_smul]; congr 1;ring

/- parley of Lap. -/
lemma parley_run (Γ:Line I)(F:Flake (n+2) I):parley (run Γ F)=∑ i,∑ j,Γ i j • parley (fun x:Tape n I=> F (Fin.cons i (Fin.cons j x))):=by
 unfold parley run lam; simp_rw [tsum_fintype,Finset.sum_smul]
 rw [Finset.sum_comm, Fintype.sum_prod_type]; apply Finset.sum_congr rfl;intro i _
 apply Finset.sum_congr rfl;intro j _
 simp only [Finset.smul_sum,smul_smul]; apply Finset.sum_congr rfl; intro x _;rw [mul_comm]

lemma unital (Γ:Line I)(V:Grain I)(n e:ℕ)(hΓ:∀ i j,Γ i j=Γ j i)(h:Forms.Sym (V e (n+2))) :
 parley (unilateral Γ V e n)=slab (half Γ) (axes I) (parley (V e (n+2))):=by
 rw [unilateral,parley_smul,lap,parley_clean,parley_run,slab_do]
 unfold axes
 simp_rw [first _ (n+1) h,Derivation.map_smul,first _ n (sym_cons h _),Finset.smul_sum,smul_smul]
 conv_rhs=>rw [Finset.sum_comm]
 apply sum_congr rfl;intro i _;apply sum_congr rfl;intro j _
 unfold half; rw [hΓ j]; congr 1; push_cast;ring

lemma interconnect (Γ:Line I)(F:Flake (p+1) I)(G:Flake (q+1) I)(hF:Forms.Sym F)(hG:Forms.Sym G):
 parley (pair Γ F G (p+q))=∑ i,∑ j, (half Γ) i j • (pderiv i (parley F)*pderiv j (parley G)):=by
 unfold pair;rw [dif_pos rfl,parley_smul]; change _ • parley (bridge _ _ _)=_
 rw [bridge,parley_clean,parley_weld]; simp_rw [first _ _ hF,first _ _ hG,Finset.smul_sum,smul_smul,smul_mul_assoc,mul_smul_comm,smul_smul]
 apply sum_congr rfl; intro i _; apply sum_congr rfl;intro j _;unfold half;congr 1;ring

lemma barren (F:Flake 0 I)(i:I):pderiv i (parley F)=0:=by
 simp only [parley,word,prod_of_isEmpty,map_sum,Derivation.map_smul,Derivation.map_one_eq_zero,smul_zero,sum_const_zero]
lemma solitary (F:Flake 1 I)(h:Forms.Sym F)(Γ:I→I→ℝ): slab Γ (axes I) (parley F)=0:=by
 simp_rw [slab_do,axes,first _ 0 h,Derivation.map_smul,barren,smul_zero,sum_const_zero]

end YM.RG08.Glyph
