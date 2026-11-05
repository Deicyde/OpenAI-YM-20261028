import Mathlib.Analysis.ODE.ExistUnique
import YM.Next.RANK.Beamers
import YM.Next.RANK.GaussTags

/-!
# Support rules for Wick propagation in finite arrays

No hand casts on covariance. Even negative displacements must supply full
comparison here on stored (periodized) rows.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function Set Lattice Wilson RG Marker  Normal MvPolynomial
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {S T U V Z : Type*}

lemma trim_sigma (q : Finset S) (P : poly S) (h : P.vars ⊆ q) : ∃ v : poly (↥q), rename (fun i:↥q=>i.val) v=P :=
  exists_rename_eq_of_vars_subset_range P _ Subtype.val_injective fun i hi=>⟨⟨_,h (show i∈P.vars from hi)⟩,rfl⟩
lemma milk_vars (Q : Normal.Symmetric S) (P : poly S) : (milk Q P).vars ⊆ P.vars:= by
  obtain ⟨H,hH⟩:=trim_sigma P.vars P le_rfl
  conv_lhs=>rw [← hH]
  rw [Normal.labelled,Normal.prepared, ← Normal.labelled]; intro i hi; obtain ⟨j,hj,h⟩:= MvPolynomial.mem_vars_rename _ _ hi; exact h ▸ j.property
lemma vars_scale (z : ℂ) (P : poly S) : (z • P).vars ⊆ P.vars:= by
  rw [← C_mul']; exact Finset.Subset.trans (vars_mul _ _) (by rw [MvPolynomial.vars_C]; simp)
lemma vars_minus [DecidableEq S] (P R : poly S) : (P-R).vars ⊆ P.vars ∪ R.vars:= by
  rw [sub_eq_add_neg]; apply Finset.Subset.trans (vars_add_subset ..); apply Finset.union_subset_union_right; rw [show -R=(-1:ℂ) • R by simp]; exact vars_scale _ _
lemma glyph_vars (i : T→₀ℂ) : (glyph i).vars ⊆ i.support:= by
  unfold glyph; rw [Finsupp.linearCombination_apply,Finsupp.sum]; intro j hj
  obtain ⟨k,hk,hh⟩:= Finset.mem_biUnion.mp (vars_sum_subset _ _ hj); have ht:= vars_scale _ (X k) hh
  rw [MvPolynomial.vars_X] at ht; exact (Finset.mem_singleton.mp ht) ▸ hk
lemma exchange_vars (x : S → T →₀ ℂ) (P : poly S) (A : Finset T) (h : ∀ i∈P.vars,(x i).support⊆ A) : (exchange x P).vars⊆A:= by
  obtain ⟨v,hv⟩:=trim_sigma P.vars P le_rfl
  suffices ∀ v : poly (↥P.vars),(exchange x (rename (fun i:↥P.vars=>i.val) v)).vars ⊆ A from hv ▸ this v
  intro p; induction p using MvPolynomial.induction_on with
  | C a=> simp only [rename_C,Normal.exchange_c,vars_C]; exact Finset.empty_subset _
  | add p q hp hq=> rw [_root_.map_add,_root_.map_add]; exact Finset.Subset.trans (vars_add_subset ..) (Finset.union_subset hp hq)
  | mul_X p i H => rw [_root_.map_mul,_root_.map_mul,rename_X,exchange_x]; exact Finset.Subset.trans (vars_mul ..) (Finset.union_subset H (Finset.Subset.trans (glyph_vars _) (h i.val i.property)))
lemma pipe_vars (x : S→T→₀ℂ) (Q : Normal.Symmetric S) (P : poly S) (A : Finset T) (h : ∀ i∈P.vars,(x i).support⊆A) : (pipe x Q P).vars⊆A := exchange_vars x (milk Q P) A fun i hi=> h i (milk_vars Q _ hi)

private lemma divide (M : Normal.Symmetric S) (P R : poly S) (h : ∀ i∈P.vars, ∀ j∈R.vars, M.cov i j=0) :
    milk M (P*R)=milk M P*milk M R:= by
  obtain ⟨q,hq⟩:=trim_sigma P.vars P le_rfl
  let Y:= (rename (fun i : P.vars=> i.val) (R:=ℂ))
  have hv (i : P.vars): slit (M.cov i.val) (milk M R)=0:= by
    obtain ⟨v,hv⟩:=trim_sigma R.vars (milk M R) (milk_vars ..)
    rw [← hv,Normal.labelled,exchange_slit]
    let f:= fun j:↥R.vars=>Finsupp.single j.val (1:ℂ)
    rw [show reads f (M.cov i.val)=0 from ?_, Normal.slit_zero,map_zero _]; funext k; rw [reads]; simp only [f,Finsupp.linearCombination_single,one_smul]; exact h _ i.property _ k.property
  have he (v : poly (↥P.vars)): milk M (Y v * R)=milk M (Y v)*milk M R:= by
    induction v using MvPolynomial.induction_on with
    | C a=> unfold Y; rw [rename_C,drink,fine]
    | add p q hp hq=> simp only [_root_.map_add,add_mul,hp,hq]
    | mul_X p i hp=>
      rw [mul_comm p,_root_.map_mul (f:=Y), show Y (X i)= X _ from rename_X ..,mul_assoc, Normal.feeds, Normal.feeds,hp]
      rw [Derivation.leibniz,hv i,smul_zero,zero_add,smul_eq_mul]; ring
  rw [show P=Y q from hq.symm]; exact he q
lemma bridge (M : Normal.Symmetric S) (H : S→T→₀ℂ) (P R : poly S) (h : ∀ i∈P.vars,∀ j∈R.vars,M.cov i j=0) : pipe H M (P*R) = pipe H M P*pipe H M R:= by rw [pipes,divide M P R h,map_mul];rfl
end YM.Next.Rank.Tapes
