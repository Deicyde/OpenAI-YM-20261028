import YM.RG08.Glyph.Scope

/-!
# Collapse the rank sums after building PDE contributions (finite tori only here).
-/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type} [Fintype I]

def showV (V:Grain I)(e:ℕ):Inn I:=∑ n∈range (e+3),parley (V e n)
def waxed (V:Grain I):Prop:=∀ e n, Forms.Sym (V e n)

omit [Fintype I] in
lemma waxed_burn {V:Grain I}(h:waxed V)(Γ:Line I)(j:ℕ):waxed (burn Γ V j):= fun e n=>by
 cases j with
 | zero=>rw [spark];exact h e n
 | succ j=>exact coal Γ V e n j

lemma gentle (V:Grain I)(h:waxed V)(hv:Eligible V)(Γ:Line I)(hΓ:∀ i j,Γ i j=Γ j i)(e:ℕ):
    ∑ n∈range (e+3), parley (unilateral Γ V e n)=slab (half Γ) (axes I) (showV V e):=by
 simp_rw [unital Γ V _ _ hΓ (h _ _)];rw [showV,map_sum]
 let T(n:ℕ):=slab (half Γ) (axes I) (parley (V e n))
 have he(n)(hh:e+2<n):T n=0:=by
   have h0:V e n=0:=Classical.not_not.mp fun h=>show False from by have :=hv.head _ _ h;omega
   simp [T,h0,parley_zero]
 have hs :T 0=0:=by simp_rw [T,slab_do,axes,barren,map_zero,smul_zero,Finset.sum_const_zero]
 have h1:T 1=0:=solitary _ (h e 1) _
 change ∑ n∈range (e+3),T (n+2)=∑ n∈range (e+3),T n
 rw [Finset.sum_range_succ (n:=e+2),Finset.sum_range_succ (n:=e+1) (f:=fun n=>T (n+2)),Finset.sum_range_succ' T (e+2),Finset.sum_range_succ' (fun i=>T (i+1)) (e+1)]
 simp [he _ (show e+2< e+1+2 by omega),he _ (show e+2<e+2+2 by omega),hs,h1]

/- Rank convolution via unique output n=p+q in marked product. -/
private lemma panel {R:Type*}[AddCommMonoid R](n:ℕ)(W:ℕ→ℕ→R)(hW:∀ i k,n < i+k→W i k=0):
 (∑ i∈range (n+1),∑ j∈range (i+1), W j (i-j))=(∑ j∈range (n+1),∑ k∈range (n+1),W j k):=by
 let S:=range (n+1)
 let T (i j k:ℕ):R:=if i=j+k then W j k else 0
 have he (i:ℕ)(hi:i≤n):∑ j∈range (i+1),W j (i-j)=∑ j∈S,∑ k∈S,T i j k:=by
    apply Eq.trans ?_ (Finset.sum_subset (range_mono (by omega:i+1≤n+1)) ?_)
    · apply sum_congr rfl;intro j hj
      simp only [mem_range] at hj
      rw [Finset.sum_eq_single_of_mem (i-j) (s:=S) (by simp [S];omega)]
      · exact (if_pos (by omega:i=j+(i-j))).symm
      intro k _ hk;exact if_neg (by omega)
    intro j _ hj; apply sum_eq_zero;intro k _;apply if_neg;simp only [mem_range] at *;omega
 calc
 _ = ∑ i∈S,∑ j∈S,∑ k∈S,T i j k:=sum_congr rfl fun i hi=>he i (by simpa [S] using hi)
 _ = ∑ j∈S,∑ k∈S,∑ i∈S,T i j k:=by rw [Finset.sum_comm];apply sum_congr rfl;intro j _; exact Finset.sum_comm
 _ = _:=by
      apply sum_congr rfl;intro j _;apply sum_congr rfl;intro k _
      by_cases hh:j+k≤n
      · rw [sum_eq_single_of_mem (j+k) (by simp [S,hh]) (fun a _ ha=>if_neg ha)];exact if_pos rfl
      rw [hW j k (by omega)];apply sum_eq_zero;intro i _;simp [T,hW j k (by omega)]

def noise (Γ:Line I)(v w:Inn I):Inn I:=∑ i,∑ j,half Γ i j • (pderiv i v*pderiv j w)
lemma square {S1 S2 T1 T2 R:Type*}[AddCommMonoid R](s:Finset S1)(t:Finset S2)(p:Finset T1)(q:Finset T2)(F:S1→S2→T1→T2→R):
 (∑ x∈s,∑ y∈t,∑ i∈p,∑ j∈q,F x y i j)=(∑ i∈p,∑ j∈q,∑ x∈s,∑ y∈t,F x y i j):=by
 rw [show (∑ x∈s,∑ y∈t,∑ i∈p,∑ j∈q,F x y i j)=∑ x∈s,∑ i∈p,∑ j∈q,∑ y∈t,F x y i j from ?_,Finset.sum_comm];apply sum_congr rfl;intro i _;exact Finset.sum_comm
 apply sum_congr rfl; intro x _;rw [Finset.sum_comm];apply sum_congr rfl;intro i _;exact Finset.sum_comm

lemma quiet (Γ:Line I)(u k:ℕ)(V T:Grain I)(hv:Eligible V)(ht:Eligible T)(wV:waxed V)(wT:waxed T):
 (∑ n∈range (u+k+3),∑ i∈range (n+1),parley (pair Γ (V u (i+1)) (T k (n-i+1)) n))=noise Γ (showV V u) (showV T k):=by
 let W (i j:ℕ):Inn I:=noise Γ (parley (V u (i+1))) (parley (T k (j+1)))
 have head (i j:ℕ)(h:i>u+1 ∨ j>k+1):W i j=0:=by
   have HE {V:Grain I}{u i:ℕ}(hV:Eligible V)(hi:i>u+1): V u (i+1)=0:=Classical.not_not.mp fun h=>show False from by have :=hV.head _ _ h;omega
   rcases h with h|h
   · simp [W,noise,HE hv h,parley_zero]
   simp [W,noise,HE ht h,parley_zero]
 have hh : (∑ n∈range (u+k+3),∑ i∈range (n+1),parley (pair Γ (V u (i+1)) (T k (n-i+1)) n))= (∑ n∈range (u+k+3),∑ i∈range (n+1), W i (n-i)):=by
    apply sum_congr rfl; intro n _; apply sum_congr rfl; intro i hi
    simp only [mem_range] at hi
    have he {p q n:ℕ}(hz:p+q=n)(F:Flake (p+1) I)(G:Flake (q+1) I)(hF:Forms.Sym F)(hG:Forms.Sym G):parley (pair Γ F G n)=noise Γ (parley F) (parley G):=by
      subst hz; exact interconnect _ _ _ hF hG
    exact he (by omega) _ _ (wV _ _) (wT _ _)
 rw [hh,panel (u+k+2) W (fun i j hi=>head i j (by omega))]
 have ha:(∑ i∈range (u+k+3),∑ j∈range (u+k+3),W i j)=∑ i∈range (u+2),∑ j∈range (k+2),W i j:=by
    symm; calc
    _ = ∑ i∈range (u+2),∑ j∈range (u+k+3),W i j:=sum_congr rfl fun i _=>sum_subset (range_mono (by omega)) fun j _ hj=>head i j (Or.inr (by simp only [mem_range] at *;omega))
    _ = _:=sum_subset (range_mono (by omega)) fun i _ hi=>sum_eq_zero fun j _=>head i j (Or.inl (by simp only [mem_range] at *;omega))
 rw [ha]
 -- need swap n,m with I,I; derivative rank zero vanishes
 unfold W noise showV

 simp_rw [map_sum,Finset.sum_range_succ' (fun n=>pderiv _ (parley (T k n))) (k+2),Finset.sum_range_succ' (fun n=>pderiv _ (parley (V u n))) (u+2),barren,add_zero,Finset.sum_mul,Finset.mul_sum,Finset.smul_sum]
 -- rectangular interchange
 exact square (range (u+2)) (range (k+2)) univ univ (fun i j l m=> _)

end YM.RG08.Glyph
