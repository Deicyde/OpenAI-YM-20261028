import YM.RG08.Glyph.Tempo

/-!
# Read moments as Wick recursions (purely algebraic, including harmonic arrays)
-/
noncomputable section
namespace YM.RG08.Glyph
open Forms Steam Cloud Finset Function MvPolynomial
open scoped BigOperators Topology Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I : Type}[Fintype I](Γ : Line I)

def radiator := slab (half Γ) (axes I)
def fork (i:I) : Inn I →ₗ[ℝ] Inn I:=∑ j,Γ i j • (pderiv j).toLinearMap
def gust (j:ℕ)(p:Inn I):Inn I:=rfactor j • (radiator Γ)^[j] p
lemma gust_dawn (p:Inn I):gust Γ 0 p=p:=by simp [gust,rfactor]
lemma gust_next (n:ℕ)(p:Inn I) : (n+1:ℝ) • gust Γ (n+1) p=radiator Γ (gust Γ n p):=by simp [gust,smul_smul,earns,Function.iterate_succ_apply']

omit [Fintype I] in
private lemma pderiv_swap (j i:I)(p:Inn I):pderiv j (pderiv i p)=pderiv i (pderiv j p):=by
 by_cases h : j = i
 · subst i
   rfl
 ext m
 simp [coeff_pderiv, Finsupp.single_eq_of_ne, h, Ne.symm h, add_comm (Finsupp.single j 1),
   add_assoc, mul_comm, mul_left_comm, mul_assoc]

lemma fork_apply (i:I)(p:Inn I):fork Γ i p=∑ j,Γ i j • pderiv j p:=by simp [fork,LinearMap.sum_apply]
lemma fork_comm (i:I)(p:Inn I):fork Γ i (radiator Γ p)=radiator Γ (fork Γ i p):=by
 rw [fork_apply,radiator,slab_do]
 conv_rhs=>rw [fork_apply,slab_do]
 unfold axes
 simp_rw [map_sum,Derivation.map_smul,Finset.smul_sum]
 have he (j a b:I):pderiv j (pderiv a (pderiv b p))=pderiv a (pderiv b (pderiv j p)):=by rw [pderiv_swap j a,pderiv_swap j b]
 simp only [smul_smul];rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro a _;rw [Finset.sum_comm];apply Finset.sum_congr rfl;intro b _;apply Finset.sum_congr rfl;intro j _;rw [mul_comm, he j a b]

lemma radiator_wave (h:∀ i j, Γ i j=Γ j i)(i:I)(p:Inn I) : radiator Γ (X i * p) = X i * radiator Γ p + fork Γ i p:=by
 rw [radiator,slab_do,slab_do,fork_apply]; unfold axes; simp only [pderiv_mul,map_add,pderiv_X,Pi.single_apply,apply_ite, pderiv_one,map_zero,ite_self,add_assoc,smul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_smul_comm]
 -- simplify crosses by sum over indicator
 simp_rw [ite_mul,one_mul,zero_mul,smul_ite,smul_zero]
 simp only [sum_const_zero,zero_add,Finset.sum_ite_eq,if_pos (mem_univ _)] -- ite_eq orientation inspect
 rw [Finset.sum_comm (f:=fun (a b:I)=>if i=a then half Γ a b • pderiv b p else 0)]
 simp only [Finset.sum_ite_eq,if_pos (mem_univ _)]
 let T(j:I):Inn I:=half Γ i j • pderiv j p
 have he (j:I):half Γ j i=half Γ i j:=by unfold half;rw [h]
 simp_rw [he]
 have hc (j:I):(Γ i j)=half Γ i j+half Γ i j:=by unfold half;ring
 conv_rhs=>arg 2; arg 2; intro j;rw [hc,add_smul]
 rw [Finset.sum_add_distrib];abel

theorem gust_wave (h:∀ i j,Γ i j=Γ j i)(i:I)(p:Inn I)(n:ℕ) :
 gust Γ (n+1) (X i*p)=X i*gust Γ (n+1) p+fork Γ i (gust Γ n p):=by
 induction n with
 | zero=>
    simp only [gust,rfactor, Function.iterate_one, Function.iterate_zero_apply,Nat.factorial_zero,Nat.factorial_one,Nat.cast_one,inv_one,one_smul,zero_add]
    exact radiator_wave Γ h ..
 | succ n ih=>
    apply Cloud.untangle (by positivity:(((n+1:ℕ):ℝ)+1)≠0)
    rw [gust_next,ih,map_add,radiator_wave Γ h,←fork_comm,smul_add,←mul_smul_comm,gust_next,add_smul,one_smul,←LinearMap.map_smul,show (((n+1:ℕ):ℝ))=(n+1:ℝ) by push_cast;rfl,gust_next]
    abel

lemma gust_add (j)(p q:Inn I):gust Γ j (p+q)=gust Γ j p + gust Γ j q:=by simp only [gust,iterate_map_add,smul_add]
lemma gust_scale (j)(a:ℝ)(p:Inn I) : gust Γ j (a • p)=a • gust Γ j p:=by
 unfold gust
 have he(j:ℕ): (radiator Γ)^[j] (a • p)=a • (radiator Γ)^[j] p:=by induction j with
 | zero=>rfl
 | succ j ih=> simp only [Function.iterate_succ_apply',ih,map_smul]
 rw [he,smul_comm]

/- eventually zero ⇒ evaluate all j at t=1. -/
def Halt (Γ:Line I)(p:Inn I)(j:ℕ) := ∀ i:ℕ,i≥j→gust Γ i p=0
lemma c_halt (a:ℝ):Halt Γ (C a) 1:=by
 intro i h;obtain ⟨i,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:i≠0)
 simp_rw [gust,Function.iterate_succ_apply]
 have he:radiator Γ (C a)=0:=by simp [radiator,slab_do,axes]
 rw [he,iterate_map_zero,smul_zero]
lemma add_halt {p q:Inn I}{n m:ℕ}(h:Halt Γ p n)(hh:Halt Γ q m):Halt Γ (p+q) (n+m):=fun i hi=>by rw [gust_add,h i (by omega),hh i (by omega),add_zero]
lemma x_halt (hΓ:∀ i j,Γ i j=Γ j i){p:Inn I}{n:ℕ}(h:Halt Γ p n)(i:I):Halt Γ (p*X i) (n+1):=by
 intro j hj; obtain ⟨j,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:j≠0)
 rw [mul_comm,gust_wave Γ hΓ,h j (by omega),h (j+1) (by omega),mul_zero,map_zero,add_zero]
lemma halts (hΓ:∀ i j,Γ i j=Γ j i)(p:Inn I):∃ n,Halt Γ p n:=by
 induction p using MvPolynomial.induction_on with
 | C=>exact ⟨1,c_halt _ _⟩
 | add _ _ hx hy=>obtain ⟨i,hx⟩:=hx;obtain ⟨j,hy⟩:=hy;exact ⟨i+j,add_halt Γ hx hy⟩ -- ?
 | mul_X _ i H=>obtain ⟨n,hp⟩:=H;exact ⟨n+1,x_halt Γ hΓ hp i⟩
end YM.RG08.Glyph
