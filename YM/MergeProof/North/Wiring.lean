import YM.MergeProof.North.Stator
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Ac Extra.Multi Corona Push GridApprox.Nil
namespace Salt
variable [Fintype I]
-- billing all marked fragments at each stamped site
lemma diced (F:I→Config G n→Poly B)(X:I→Support n)(w:V→ℝ)(α K:ℝ)(m:ℕ)(hw:∀ i,0<w i)(h:Towed w X F m α K): ∃ v:I×B.Mode→ℝ, (∀ i,0 ≤ v i)∧(∀ i U,‖(F i.1 U).part i.2‖ ≤ v i) ∧ Hit (X ∘ Prod.fst) m (fun i=>Poly.toll w i.2*v i) α K:=by
   obtain ⟨a,_,hp,hf⟩:=h
   choose v hv hV hR using hf
   refine ⟨fun i=> v i.1 i.2,fun i=> hv ..,fun i _=> hV ..,fun i=> ?_⟩
   refine ⟨fun j=> ?_,Summable.of_finite,?_⟩
   · dsimp only; split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hv ..)) (Real.exp_pos _).le; rfl
   rw [tsum_fintype,Fintype.sum_prod_type];
   refine le_trans (sum_le_sum ?_) (Budget.cap (hp i) univ); intro b _
   by_cases he:i∈ X b
   · change (∑ j:B.Mode,if _ ∈ _ then _ else _) ≤ if i∈X b then a b*Real.exp (α*coverNumber m (X b)) else 0
     simpa only [wordsPrice,comp_apply,he,↓reduceIte,← sum_mul] using (mul_le_mul_of_nonneg_right (hR b) (Real.exp_pos (α *coverNumber m (X b))).le : _)
   dsimp only [comp_apply]; simp [he]
omit [Fintype I]
variable (Z:Salt V G n)(w:Name V→ℝ)(α g :ℝ)(l m:ℕ)(hw:∀ i,0<w i)(h:Occupancy Z.grain l)(hg:∀ i,w i*‖Z.pepper i‖ ≤ g)(hm:0<m)
include hw h hg hm
lemma paperRate (a:ℝ)(hg':0≤ g)(ht:Towed w id Z.air m α a)(ha:0 ≤ α) :
    ∃ y:Z.Lawn→ℝ, (∀ i,0 ≤ y i)∧(∀ i U,‖Z.syrup i U‖ ≤ y i) ∧ Hit Z.leaf m (fun i=>Poly.toll w (Z.marker i)*y i) α (l*g*Real.exp α+a):=by
   obtain ⟨v,hv,hx,hV⟩:= diced _ _ w α a m hw ht
   let F:= fun j:Z.Lawn=> Sum.elim (fun i=>‖Z.pepper i‖) (fun i=>v i.val) j
   have hz i : 0 ≤ F i:=by cases i; exact norm_nonneg _; next i=> exact hv i.val
   refine ⟨F,hz,fun i=>?_,fun i=>?_⟩
   · cases i
     next i=> exact fun _=> le_rfl
     next i=> exact hx i.val
   let f j:=if i∈ Z.leaf j then Poly.toll w (Z.marker j)*F j * Real.exp (α*coverNumber m (Z.leaf j)) else 0
   have hf j:0≤f j:=by unfold f; split; exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (hz _)) (Real.exp_pos _).le; exact le_rfl
   change SumBudget f _
   refine ⟨hf,Summable.of_finite,?_⟩; rw [tsum_fintype,Fintype.sum_sum_type]
   refine add_le_add ?_ ?_
   · let p:= univ.filter (fun j=> Z.grain j=i)
     have hx : ∑ j, f (.inl j)= ∑ j∈p,f (.inl j):=(sum_subset (filter_subset ..) (fun j hj h=> if_neg (fun e=> h (mem_filter.mpr ⟨hj,(mem_singleton.mp e).symm⟩)))).symm
     rw [hx];
     trans ∑ j ∈ p, g*Real.exp α
     · apply sum_le_sum; intro j hj; have he:= (mem_filter.mp hj).2; unfold f leaf; simp only [Sum.elim]; rw [if_pos (mem_singleton.mpr he.symm : i∈Z.leaf (.inl j)),marker,Sum.elim_inl,Poly.solo_toll]
       let x:=Z.grain j; have hx: coverNumber m {x} ≤ 1:= (Corona.cover_mono (Lattice.halo_subset 0 {x}) m).trans (show coverNumber m (Lattice.halo 0 {x}) ≤ _ from by simpa using Corona.tile x 0 m hm)
       exact mul_le_mul (hg j) (Real.exp_monotone (mul_le_of_le_one_right ha (Nat.cast_le_one.mpr hx))) (Real.exp_pos _).le hg'
     rw [sum_const,nsmul_eq_mul, mul_assoc]; gcongr; exact h i
   have hp:= Budget.pull_le (q:=fun i:Z.Turf=>i.val) (p:=fun _=>True) (hV i) (fun i=>hf (Sum.inr i)) (fun _ _=>trivial) Subtype.val_injective.injOn (fun i _=> le_rfl)
   exact Budget.cap hp univ
end Salt
end YM.MergeProof.Ribbons
