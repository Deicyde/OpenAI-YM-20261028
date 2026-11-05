import YM.RG08.Glyph.Wind

/-! Ordinary partial Wick pairings of field polynomials on finite gluing layers. -/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type}[Fintype I]{Γ : Line I}

def wick (Γ:Line I)(p:Inn I):Inn I:= if h : ∃ n,Halt Γ p n then ∑ i∈range (Classical.choose h), gust Γ i p else 0
lemma wick_budget {p:Inn I}{n:ℕ}(h:Halt Γ p n):wick Γ p=∑ j∈range n,gust Γ j p:=by
 let ht:∃ n,Halt Γ p n:=⟨n,h⟩;rw [wick,dif_pos ht]
 let m:=Classical.choose ht; have he:Halt Γ p m:=Classical.choose_spec ht
 change ∑ i∈range m,gust Γ i p=_
 rcases le_total n m with hh|hh
 · exact (sum_subset (range_mono hh) fun i _ hi=>h i (by simp only [mem_range] at hi; omega)).symm
 exact sum_subset (range_mono hh) fun i _ hi=>he i (by simp only [mem_range] at hi;omega)

lemma wick_add (hΓ:∀ i j,Γ i j=Γ j i)(p q:Inn I):wick Γ (p+q)=wick Γ p+wick Γ q:=by
 obtain ⟨m,hm⟩:=halts Γ hΓ p;obtain ⟨n,hn⟩:=halts Γ hΓ q
 rw [wick_budget (add_halt Γ hm hn), wick_budget (p:=p) (n:=m+n) (fun i hi=>hm i (by omega)),wick_budget (p:=q) (n:=m+n) (fun i hi=>hn i (by omega)),←sum_add_distrib]; simp_rw [gust_add]
lemma wick_scale (hΓ:∀ i j,Γ i j=Γ j i)(a:ℝ)(p:Inn I):wick Γ (a • p)=a • wick Γ p:=by
 obtain ⟨m,hm⟩:=halts Γ hΓ p
 have he:Halt Γ (a • p) m:=fun i hi=>by simp only [gust_scale,hm i hi,smul_zero]
 rw [wick_budget he,wick_budget hm,Finset.smul_sum];simp_rw [gust_scale]
lemma wick_fork (hΓ:∀ i j,Γ i j=Γ j i)(i:I)(p:Inn I):wick Γ (fork Γ i p)=fork Γ i (wick Γ p):=by
 have he (j:ℕ)(p:Inn I) : gust Γ j (fork Γ i p)=fork Γ i (gust Γ j p):=by
   unfold gust; rw [LinearMap.map_smul]
   congr 1; induction j with
   | zero=> rfl
   | succ j hj=>rw [Function.iterate_succ_apply',hj,←fork_comm,Function.iterate_succ_apply']
 obtain ⟨n,hn⟩:=halts Γ hΓ p
 have hp:Halt Γ (fork Γ i p) n:=fun j hj=>by rw [he,hn j hj,map_zero]
 rw [wick_budget hn,wick_budget hp,map_sum];simp_rw [he]
lemma wick_x (hΓ:∀ i j,Γ i j=Γ j i)(p:Inn I)(i:I):wick Γ (X i*p)= X i*wick Γ p+wick Γ (fork Γ i p):=by
 obtain ⟨n,hn⟩:=halts Γ hΓ p
 rw [wick_fork hΓ, mul_comm (X i) p, wick_budget (x_halt Γ hΓ hn i),wick_budget (Γ:=Γ) (p:=p) (n:=n+1) (fun i hi=>hn i (by omega))]
 rw [sum_range_succ' (fun j=>gust Γ j (p*X i)),mul_comm p (X i)]
 simp_rw [gust_wave Γ hΓ i p,Finset.sum_add_distrib,map_sum,gust_dawn,Finset.mul_sum]
 conv_rhs=> arg 2;rw [sum_range_succ,hn n le_rfl,map_zero,add_zero]
 conv_rhs=> arg 1;rw [sum_range_succ',gust_dawn]
 abel
lemma wick_c (a:ℝ):wick Γ (C a)=C a:=by rw [wick_budget (c_halt Γ a),sum_range_one,gust_dawn]

def wind (Γ:Line I)(hΓ:∀ i j,Γ i j=Γ j i):Inn I→ₗ[ℝ] Inn I where
 toFun:=wick Γ
 map_add':=wick_add hΓ
 map_smul':=wick_scale hΓ

/- show literally evaluates all matchings (incl singleton option). `s` indexed by an external
Finset; recursion at any chosen position, hence e.g. a canonical first location at every step
enumerates exactly all partial pairings. Use AlgHom substitution afterwards for viewing surviving
letters at the appropriate mean.
-/
def stack {M:Type}(s:Finset M)(f:M→I):Inn I:=∏ i∈s,X (f i)
lemma fork_stack {M:Type}(s:Finset M)(f:M→I)(i:I):fork Γ i (stack s f)=∑ x∈s,Γ i (f x) • stack (s.erase x) f:=by
 have hx(t:M):fork Γ i (X (f t))= C (Γ i (f t)):=by
    rw [fork_apply];simp only [pderiv_X,Pi.single_apply,smul_ite,smul_zero,sum_ite_eq,if_pos (mem_univ _)]
    rw [Algebra.smul_def,mul_one];rfl
 have hm (u v:Inn I):fork Γ i (u*v)=fork Γ i u*v+u*fork Γ i v:=by simp only [fork_apply,pderiv_mul,Finset.sum_mul,Finset.mul_sum,smul_add,Finset.sum_add_distrib,smul_mul_assoc,mul_smul_comm]
 induction s using Finset.induction_on with
 | empty=>simp [fork_apply,stack]
 | insert a s ha ih=>
    rw [stack,prod_insert ha,hm,hx,show (∏i∈s,X (f i):Inn I)=stack s f from rfl,ih,Finset.sum_insert ha,Finset.erase_insert ha,Finset.mul_sum]
    congr 1
    · rw [Algebra.smul_def];rfl
    apply Finset.sum_congr rfl;intro x hx;rw [Finset.erase_insert_of_ne (by rintro rfl;exact ha hx),stack,stack,prod_insert (fun hh=>ha (Finset.mem_of_mem_erase hh)),mul_smul_comm]

/-- Isserlis recursion including unpaired branch and Wick prices, any fixed occurrence s. Together
with linearity this pins the independent prescription. No unlabeled-symmetry divisors. -/
theorem wick_occurrences (hΓ:∀ i j,Γ i j=Γ j i){M:Type}(s:Finset M)(f:M→I){i:M}(hi:i∈s): wind Γ hΓ (stack s f)= X (f i)*wind Γ hΓ (stack (s.erase i) f)+∑ j∈s.erase i,Γ (f i) (f j) • wind Γ hΓ (stack ((s.erase i).erase j) f):=by
 have he (p):wind Γ hΓ p=wick Γ p:=rfl
 have hz:stack s f=X (f i)*stack (s.erase i) f:=(Finset.mul_prod_erase s _ hi).symm
 rw [hz,he,wick_x hΓ,fork_stack]
 simp_rw [← he,map_sum,map_smul]
theorem wick_empty (hΓ : ∀ i j,Γ i j=Γ j i){M:Type}(f:M→I):wind Γ hΓ (stack ∅ f)=1:=by
 simp only [stack,prod_empty];exact wick_c (Γ:=Γ) 1 -- C_one defeq?
end YM.RG08.Glyph
