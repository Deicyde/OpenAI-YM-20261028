import YM.MergeProof.North.Wiring
import YM.OPE.Grouping.Fibers
import YM.OPE.Grouping.Stator

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/Wiring.lean
to a projection along fibers. The Deck prices a nonempty finite number of children
(not necessarily common across grouping regions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀][DecidableEq S₀] {Δ : Fibers S₀ V}
open Ac Extra.Multi Corona Push GridApprox.Nil
namespace Salt
variable (Z:Salt V S₀ Δ G n)(w:S₀→ℝ)(α g :ℝ)(l m:ℕ)(hw:∀ i,0<w i)(h:Occupancy Z.grain l)(hg:∀ i,w i * ‖Z.pepper i‖ ≤ g)(hm : 0 < m)
include hw h hg hm
lemma paperRate (a:ℝ)(hg':0≤ g)(ht:Towed w id Z.air m α a)(ha:0 ≤ α) :
    ∃ y:Z.Lawn→ℝ, (∀ i,0 ≤ y i)∧(∀ i U,‖Z.syrup i U‖ ≤ y i) ∧ Hit Z.leaf m (fun i=>Poly.toll w (Z.marker i)*y i) α (l*g*Real.exp α+a):=by
   obtain ⟨v,hv,hx,hV⟩:= YM.MergeProof.Ribbons.Salt.diced _ _ w α a m hw ht
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
end YM.MergeProof.Ribbons.Fibers
