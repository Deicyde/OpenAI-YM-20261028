import YM.RG08.Carrel.Polar
import YM.RG08.Aggregate.Spice
import Mathlib.Algebra.Polynomial.Roots

/-!
# quantitative multidiagonal extraction at fixed arity budgets

universal over x families/cutoff, can spend任意 pre-L fees. no compactness on parameter
scale needed. Handles n=0.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.Flint
open Forms Function Finset Filter Carrel Camera MvPolynomial Glyph
open scoped BigOperators Classical Topology
variable {I:Type}{R n:ℕ}

open Polynomial in
lemma sounds {p:Fin (R+1)→ℝ}(hp:∀ c:ℝ,∑ i:Fin (R+1),c^i.val*p i=0):p=0:=by
 let m:=∑ i:Fin (R+1),Polynomial.monomial i.val (p i)
 have h:m=0:=by
    apply Polynomial.funext; intro c
    simp only [m,eval_finsetSum,Polynomial.eval_monomial,Polynomial.eval_zero]; simpa only [mul_comm] using hp c
 funext i
 refine (show m.coeff i.val=p i from ?_).symm.trans (by simp [h])
 simp only [m,finsetSum_coeff,Polynomial.coeff_monomial]
 rw [sum_eq_single_of_mem i (mem_univ _)]; simp
 intro j _ hj;simp [Fin.val_inj,hj]

def RangeTape (I:Type)(R:ℕ):Submodule ℝ ((i:Fin (R+1))→Flake i.val I) where
 carrier:={x|∀ i,Forms.Sym (x i)}
 zero_mem':=fun _=>Sym.zero
 add_mem':=fun ha hb _=>(ha _).add (hb _)
 smul_mem':=fun c _ ha _=>(ha _).smul c
abbrev Shifter (I:Type)(R:ℕ):=↥(RangeTape I R)
variable [Fintype I]

def pitches (x:I→ℝ):Module.Dual ℝ (Shifter I R):=
  ∑ i:Fin (R+1), (Aggregate.street I x).comp ((Aggregate.parlin i.val I).comp ((LinearMap.proj (R:=ℝ) (φ:=fun i:Fin (R+1)=>Flake i.val I) i).comp ((RangeTape I R).subtype)))
lemma pitches_apply (x:I→ℝ)(M:Shifter I R): pitches x M = ∑ i:Fin (R+1),MvPolynomial.eval x (parley (M.val i)):=by
 rw [pitches,LinearMap.sum_apply];rfl
lemma parley_street (x:I→ℝ)(M:Flake n I): MvPolynomial.eval x (parley M)=∑ t:Tape n I,M t*∏ j,x (t j):=by
 unfold parley;rw [map_sum];simp_rw [word,MvPolynomial.smul_eq_C_mul,MvPolynomial.eval_mul,eval_C,map_prod,eval_X]
lemma unroll (x:I→ℝ)(a:ℝ)(M:Flake n I): MvPolynomial.eval (a • x) (parley M)=a^n*MvPolynomial.eval x (parley M):=by
 simp_rw [parley_street, Pi.smul_apply,smul_eq_mul,prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,mul_sum];apply sum_congr rfl; intro t _; ring
omit [Fintype I] in
lemma hub (x:Shifter I R):∀ e:Fin (R+1),Forms.Sym (x.val e):=x.property
lemma pitches_detect (v:Shifter I R)(he:∀ x:I→ℝ,pitches x v=0):v=0:=by
 simp_rw [pitches_apply] at he;apply Subtype.ext;funext i
 apply Carrel.pursuit (hub v i) Forms.Sym.zero; apply MvPolynomial.funext
 intro x; rw [parley_zero,map_zero]
 have h:=sounds (p:=fun i:Fin (R+1)=>MvPolynomial.eval x (parley (v.val i))) (fun c=>by simpa only [unroll] using he (c • x))
 exact congrFun h i

lemma pitches_full (f:Module.Dual ℝ (Shifter I R)):f∈Submodule.span ℝ (Set.range (pitches (I:=I) (R:=R))):=by
 let Q:=Submodule.span ℝ (Set.range (pitches (I:=I) (R:=R)))
 change f∈Q; rw [←Subspace.dualCoannihilator_dualAnnihilator_eq (W:=Q)]
 apply (Submodule.mem_dualAnnihilator _).mpr
 intro y hy;unfold Q at hy;rw [←SetLike.mem_coe,Submodule.coe_dualCoannihilator_span] at hy
 rw [pitches_detect _ (fun x=>hy _ ⟨x,rfl⟩),map_zero]

lemma comes (f:Module.Dual ℝ (Shifter I R))(W:(I→ℝ)→ℝ): ∃ C:ℝ,0≤C∧∀ (B:ℝ)(x:Shifter I R),0≤B→ (∀ u,|pitches u x|≤W u*B)→|f x|≤C*B:=by
 let p (f:Module.Dual ℝ (Shifter I R)) (_:f∈Submodule.span ℝ (Set.range pitches)):=∃ C:ℝ,0≤C∧∀ (B:ℝ)(x:Shifter I R),0≤B→ (∀ u,|pitches u x|≤W u*B)→|f x|≤C*B
 refine Submodule.span_induction (p:=p) ?_ ⟨0,le_rfl,by simp⟩ (fun a b _ _ ha hb=>?_) (fun t a _ h=>?_) (pitches_full f)
 · rintro _ ⟨x,rfl⟩;exact ⟨|W x|,abs_nonneg _,fun B y hy H=>(H x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hy)⟩
 · obtain ⟨C,hC,ha⟩:=ha;obtain ⟨D,hD,hb⟩:=hb;refine ⟨C+D,add_nonneg hC hD,fun B x hx ht=>?_⟩
   rw [LinearMap.add_apply,add_mul];exact (abs_add_le ..).trans (add_le_add (ha B x hx ht) (hb B x hx ht))
 obtain ⟨C,hC,hC'⟩:=h;refine ⟨|t| * C,mul_nonneg (abs_nonneg _) hC,fun B x hx ht=>?_⟩
 rw [LinearMap.smul_apply,smul_eq_mul,abs_mul,mul_assoc];exact mul_le_mul_of_nonneg_left (hC' B x hx ht) (abs_nonneg _)

/-- all-direction evaluations for all degrees together, assuming only a symmetry.
W arbitrary announced pointwise tariff. Constant uniform before all blocks. No convergence needed.
-/
theorem septet (W:(I→ℝ)→ℝ)(hn:n≤R)(z:Tape n I):∃ C:ℝ,0≤C∧∀ (B:ℝ)(f:(k:ℕ)→Flake k I),0≤B→(∀ i≤R,Forms.Sym (f i))→
   (∀ u:I→ℝ,|∑ i∈range (R+1),∑ x:Tape i I, f i x * ∏ j:Fin i,u (x j)| ≤ W u * B)→ |f n z| ≤ C*B:=by
 let i:Fin (R+1):=⟨n,by omega⟩
 let q:Module.Dual ℝ (Shifter I R):=(LinearMap.proj (φ:=fun _:Tape n I=>ℝ) z).comp ((LinearMap.proj i).comp (RangeTape I R).subtype) -- i.val=n def
 obtain ⟨C,hC,H⟩:=comes q W;refine ⟨C,hC,fun B f hB he hu=>H B ⟨fun x=>f x.val,fun i=>he i.val (by omega)⟩ hB ?_⟩
 intro u; specialize hu u; simp only [pitches_apply,parley_street]; rw [Fin.sum_univ_eq_sum_range (fun i=>∑ x:Tape i I,f i x*∏ j:Fin i,u (x j)) (R+1)]; exact hu
end YM.RG08.Flint
