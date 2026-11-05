import YM.RG08.Spar.Peek

noncomputable section
namespace YM.RG08.Spar
open Forms Rudder Packets Finset Function Lattice Laurent Pert.Bulk Exterior Filter Bloch Anchor Symmetry Isles Stationary RG Rows
open scoped Topology BigOperators Classical ENNReal Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {I:Type}[Fintype I] {n:ℕ}{P:Side}{σ C:ℝ}

lemma transitive {X Y Z:Type}[Fintype X][Fintype Y](A:Matrix X Y ℝ)(B:Matrix Y Z ℝ)(F:Flake n X):
 query B (query A F)=query (A*B) F:=by
 ext u;unfold query;simp_rw [sum_mul]; rw [Finset.sum_comm];apply sum_congr rfl;intro i _
 simp_rw [Matrix.mul_apply];rw [Fintype.prod_sum,Finset.mul_sum];apply sum_congr rfl;intro j _;rw [Finset.prod_mul_distrib,mul_assoc]

-- Color testing helper for packed, includes Co matrices on unequal Side
abbrev cap (I:Type)(P:Side)(k:ℕ):=Co P (Kind I k)
def shaded{K H:Type}(c d:Side)(V:Type)(M:Matrix (Co c K) (Co d H) ℝ):Matrix (Co c (K×V)) (Co d (H×V)) ℝ :=Matrix.of fun x z=>if x.2.2=z.2.2 then M (x.1,x.2.1) (z.1,z.2.1) else 0
private def puff (k:ℕ)(P:Side)(I:Type):Body k P× I≃cap I P k :=Equiv.prodAssoc ..
private lemma color_query (k u:ℕ)(z:Side)(c:Tape n (cap I z u))(M:Matrix (Body k P) (Body u z) ℝ)(T:Flake n (cap I P k)):
 query (shaded P z I M) T c =∑ y:Tape n (Body k P), T (fun j=> ((y j).1,(y j).2,(c j).2.2))* ∏ j,M (y j) ((c j).1,(c j).2.1):=by
 unfold query
 rw [←Equiv.sum_comp (carton n _ _ (puff k P I)) (fun y=>T y*∏ j,shaded P z I M (y j) (c j))]
 let U:Tape n (Body k P × I)≃Tape n (Body k P)×Tape n I:={ toFun x:=(fun j=>(x j).1,fun j=>(x j).2),invFun x:=fun j=>(x.1 j,x.2 j),left_inv _:=rfl,right_inv _:=rfl}
 rw [←Equiv.sum_comp U.symm (fun y=>T _*∏ j,_)];rw [Fintype.sum_prod_type]
 apply sum_congr rfl; intro x _
 let y:Tape n I:=fun j=>(c j).2.2
 rw [Finset.sum_eq_single y]
 · change T _ * (∏ j, if y j=(c j).2.2 then _ else 0)=_
   simp only [y,ite_true];rfl
 · intro b _ hb;obtain ⟨j,hj⟩:=Function.ne_iff.mp hb
   apply mul_eq_zero_of_right; apply Finset.prod_eq_zero (mem_univ j)
   change (if b j=(c j).2.2 then _ else 0)=0;exact if_neg hj
 simp

/- finite curl on all slots of a periodized U -/
lemma descend {F:Raw I n}(i:Fin n)(h:NextTo F σ C):
 pour (P:=P) (compress 1 (picture I n F)) i=query (shaded P P I ((cobound 1).acts P)) (pour (compress 2 F) i):=by
 funext y;rw [color_query]
 let f(j:Fin n): Sampler 1 P:=Pi.single ((y j).1,(y j).2.1) 1
 have he:=compact_curls i h (fun j=>(y j).2.2) f
 apply Eq.trans _ (he.trans ?_)
 · let x:Tape n (Body 1 P):=fun j=>((y j).1,(y j).2.1)
   rw [Finset.sum_eq_single x]
   · simp [x,f]
   · intro b _ hb;obtain ⟨j,hj⟩:=Function.ne_iff.mp hb
     apply mul_eq_zero_of_right;apply Finset.prod_eq_zero (mem_univ j);apply Pi.single_eq_of_ne hj
   simp
 simp [f,Matrix.mulVec_single]

end YM.RG08.Spar
