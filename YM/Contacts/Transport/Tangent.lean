import YM.Contacts.Solstice.Suture
/-! # Multilinearity in the originally assigned grade list

When using in field frames and finite sums. Each occurrence is initially homogenous in the
splitting, so the degrees are registered once for the entire occurrence. These statements show
linearity in the operation under that assignment, even for nested horizons, before making changes
of field involving multiple grades. In particular this is not a nonlinear rule based on picking
new divergent indices from the arguments of the map under an expansion.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Transport
open Function Set Metric MeasureTheory Table Spec Normal MultipleContact OPE Harvest Route Solstice Ordered
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace MeasureTheory
variable {I F X : Type} [AddCommGroup X][Module ℂ X][AddCommGroup F][Module ℂ F]

-- one slot homogeneity

def GradeMap (f : X → F) := ∃ F' : X→ₗ[ℂ] F,f=⇑F'
def Elastic (p : Prop)(f : X→ F) := (p → GradeMap f) ∧ (¬p→ ∀ x y, f x=f y)
variable {f g : X→ F}{P Q : Prop}
namespace Elastic
lemma propagates {E : Type}[AddCommGroup E][Module ℂ E](h : Elastic P f)(A : F→ₗ[ℂ] E) : Elastic P (A ∘ f):= ⟨fun p=>by obtain ⟨r,h⟩:= h.1 p; rw [h]; exact ⟨A.comp r,rfl⟩,fun p u v=>congrArg A (h.2 p u v)⟩
lemma zero : Elastic P (f:= (0 : X → F)):= ⟨fun _=> ⟨0,rfl⟩,fun _ _ _=> rfl⟩
lemma one (A:F) : Elastic False (fun _:X=>A):= ⟨False.elim,fun _ _ _=>rfl⟩
lemma yes (F:X→ₗ[ℂ] F) : Elastic True F:= ⟨fun _=>⟨F,rfl⟩,fun h=>(h trivial).elim⟩
lemma lift (h : Elastic P f) (hp : Q↔ P) : Elastic Q f:= (propext hp).symm ▸ h
lemma plus (h : Elastic P f)(k : Elastic P g): Elastic P (f+g):= by
   refine ⟨fun p=> ?_, fun p x y=> by rw [Pi.add_apply,Pi.add_apply,h.2 p x y,k.2 p x y]⟩; obtain ⟨r,rfl⟩:= h.1 p; obtain ⟨t,rfl⟩:= k.1 p; exact ⟨r+t,rfl⟩
lemma sum (p:Finset I) {A : I → X→ F} (h : ∀ i∈p,Elastic P (A i)) : Elastic P (fun x=> ∑ i∈p,A i x):= by induction p using Finset.induction with
  | empty=> simp_rw [Finset.sum_empty]; exact zero
  | insert i p hi ih=> simp_rw [Finset.sum_insert hi]; exact plus (h i (by simp)) (ih (fun j hj=> h _ (Finset.mem_insert_of_mem hj)))
-- when multiplying disjoint blocks, degree match for the tested column in only one block
end Elastic
section Ring
variable {R : Type} [Ring R][Algebra ℂ R]
lemma Elastic.times {f g:X→R}(h : Elastic P f)(hh : Elastic Q g)(he : P→ Q→False) : Elastic (P∨Q) (f*g):= by
   suffices ht : GradeMap f → (∀ x y,g x=g y) → GradeMap (f*g) by
      refine ⟨fun p=> ?_,fun p x y=>by simp only [Pi.mul_apply,h.2 (fun h=> p (.inl h)) x y,hh.2 (fun k=> p (.inr k)) x y]⟩
      rcases p with hA|hA; exact ht (h.1 hA) (hh.2 (he hA)); obtain ⟨t,ht⟩:= hh.1 hA; refine ⟨(LinearMap.mulLeft ℂ (f 0)).comp t,funext fun x=> ?_⟩; rw [Pi.mul_apply,h.2 (fun e=>he e hA) x 0,ht]; rfl
   rintro ⟨q,hq⟩ hm; refine ⟨(LinearMap.mulRight ℂ (g 0)).comp q,funext fun x=> ?_⟩; rw [Pi.mul_apply,hm x 0,hq]; rfl
end Ring
variable {E : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {k : ℕ}{G:Gauge}{C:Family G}{Ord:Extraction.Order}{S:Table C.book}{Z:Final C Ord S}{d : Fin k→ℕ}
local notation "V!" => Expression Z.sector.derivatives
local notation "GN" => Normal.Group k
section Credit
variable {V : Type}[Ring V][Algebra ℂ V] {p : Fin k}
private lemma indep_ids (f : GN → X→ V)(Q : Finset GN)(h : ∀ x,(Q:Set GN).Pairwise fun i j=> Commute (f i x) (f j x))(hh : ∀ i∈Q,Elastic (p∈i) (f i)) (hp : (Q:Set GN).PairwiseDisjoint id) : Elastic (p∈ Q.biUnion id) (fun x=>Ordered.product Q (fun j=>f j x)):= by
   induction Q using Finset.induction with
   | empty=> simp_rw [Finset.biUnion_empty,Finset.notMem_empty,Ordered.product_empty]; exact Elastic.one 1 -- false?
   | insert i Q hi ih=>
     have he := Finset.coe_subset.mpr (Finset.subset_insert i Q); rw [Finset.biUnion_insert]; have hm : p∈ (id i ∪ Q.biUnion id) ↔ p∈ i ∨ p∈ Q.biUnion id:= Finset.mem_union;
     simp_rw [Ordered.product_insert (s:=Q) (i:=i) _ hi (h _)] -- use times
     refine Elastic.lift ( Elastic.times (X:=X) (P:=p∈i) (hh i (by simp)) (ih (fun x=>(h x).mono he) (fun j hj=> hh _ (he hj)) (hp.subset he)) (fun p' ht=>?_)) hm
     obtain ⟨j,hj,h⟩:= Finset.mem_biUnion.mp ht; exact Finset.disjoint_left.mp (hp ( (show i∈ (↑(insert i Q):Set GN) from by simp)) (he hj) (fun h=> hi (h ▸ hj))) p' h
lemma pack_trees (f : GN→ X→ V) (g:GN)(Q : Pieces g) (h : ∀ x,(Q.parts:Set GN).Pairwise fun i j=> Commute (f i x) (f j x))(hh : ∀ i∈Q.parts,Elastic (p∈i) (f i)) : Elastic (p∈g) (fun x=>parcel (fun j=> f j x) Q):= Elastic.lift (indep_ids f Q.parts h hh Q.disjoint) (by rw [Q.biUnion_parts])
end Credit

variable (M : Devices Z.sector.derivatives) (o:Points k)(P:E→ₗᵢ[ℝ] Points k)
variable (s:ℝ)(z:Cells S d)(i:Fin k)
def colors (x:S.Field (d i)):= waySystem P M o d (Function.update z i x)
omit [FiniteDimensional ℝ E] in
lemma at_leaf (j:Fin k) : Elastic (i=j) (fun x=> ((colors M o P z i x).field j ⊗ₜ[ℂ] (1:Optical E))):= by
   constructor; swap; · intro h x y; simp [colors,waySystem,Function.update_of_ne (Ne.symm h)]
   intro hi; subst j; let F:= LinearMap.pi (fun x:E=>insertField M.basis ((P x+o) i) (d i)); let K:(E→V!) →ₐ[ℂ] Score E V! := Algebra.TensorProduct.includeLeft; refine ⟨K.toLinearMap.comp F, funext fun x=>?_⟩; simp only [colors,waySystem, Function.update_self]; rfl
lemma subTangent (g:GN) (F : S.Field (d i) → Score E V!) (h : Elastic (i∈g) F): Elastic (i∈g) (fun x=> (colors M o P z i x).subtractAt P s g (F x)):= by
    let X (j : Fin (levels d g)):=(LinearMap.mulRight ℂ (instructionScore E V! (taylor (normalOn P g) s ((levels d g)-1-j.val)))).comp (reshape (fun x=>M.insertRow (centroid g (P x+o)) j)) -- arguments
    have he:= Elastic.sum Finset.univ (fun j (_:j∈Finset.univ)=> Elastic.propagates h (X j)) -- specify A
    apply Elastic.propagates he (-(LinearMap.id : Score E V!→ₗ[ℂ] Score E V!))
lemma one_channel (g:GN) (hg:g.Nonempty): Elastic (i∈g) (fun x=> (colors M o P z i x).cumulant P s g):=by
    induction g using Finset.strongInductionOn with
    | _ g ih=>
      by_cases hm:1< g.card; swap
      · obtain ⟨j,rfl⟩:= Finset.card_eq_one.mp (show g.card=1 from le_antisymm (not_lt.mp hm) hg.card_pos);
        simp_rw [System.single_op]; exact (at_leaf M o P z i j).lift Finset.mem_singleton
      simp_rw [System.equation_subtract P _ s g hm]; apply subTangent
      refine Elastic.sum (Finset.univ.erase (⊤:Pieces g)) fun u hu=>?_ ;
      exact pack_trees (fun j x=> (colors M o P z i x).cumulant P s j) g u (fun x=> ((colors M o P z i x).compatible P s).stands u) (fun j hj=> ih j (inner_piece u (Finset.mem_erase.mp hu).1 hj) (u.nonempty_of_mem_parts hj))
lemma across (g:GN)(K : Pieces g) : Elastic (i∈g) (fun x=> parcel ((colors M o P z i x).full P s) K):= by
    let f(j:GN)(x):=(colors M o P z i x).cumulant P s j; have he(Q:GN) : Elastic (i∈Q) (fun x=> (colors M o P z i x).full P s Q):= Elastic.sum (Finset.univ) fun a (_:a∈(Finset.univ:Finset (Pieces Q)))=> pack_trees f _ a (fun x=> ( (colors M o P z i x).compatible P s).stands a) (fun j hj=>one_channel M o P s z i j (a.nonempty_of_mem_parts hj))
    exact pack_trees (fun j x=>(colors M o P z i x).full P s j) _ K (fun x=> ( (colors M o P z i x).can_use P s).stands K) fun j hj=> he j
end YM.Contacts.Transport
