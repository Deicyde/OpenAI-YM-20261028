import YM.Extra.MULTISOURCE_TRAJECTORIES.Packets
import YM.MergeProof.Accent

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable {P:BudgetPoint} (A:Activities G n) {B:Census V}
-- pattern general. valid Barcode pairs when theory enabled
lemma marked_pattern [DecidableEq I] (σ : I→Box n)(s:Support n)(p:Finset I)(hs:∀ i∈p,((σ i).1).Nonempty): Packets.selected σ (Pattern s) p ↔ (p:Set I).PairwiseDisjoint (fun i=> (σ i).1) ∧ p.biUnion (fun i=>(σ i).2)=s:=by
   have hu : (p.image σ).biUnion Prod.snd=p.biUnion (fun i=> (σ i).2):=by rw [image_biUnion]
   unfold Packets.selected Pattern; rw [hu]; constructor
   · rintro ⟨⟨ht,hp⟩,he⟩; exact ⟨fun i hi j hj hx=> ht (Finset.mem_image_of_mem _ hi) (Finset.mem_image_of_mem _ hj) (fun hh=> hx (he hi hj hh)),hp⟩
   rintro ⟨hv,h⟩; refine ⟨⟨?_,h⟩,fun i hi j hj he=> ?_⟩
   · rintro b hb c hc hh; obtain ⟨i,hi,rfl⟩:= Finset.mem_image.mp hb; obtain ⟨j,hj,rfl⟩:= mem_image.mp hc; exact hv hi hj (fun h=>hh (congr_arg _ h))
   by_contra hx; obtain ⟨k,hk⟩:=hs i hi;exact Finset.disjoint_left.mp (hv hi hj hx) hk (show k∈(σ j).1 from he ▸ hk)
lemma field_eq (k:I→Box n)(s:Support n) (f:I→Poly B)(h: Summable f)(hc: Summable (Packets.value k (Pattern s) f)): field (cram k f) s=∑' j, Packets.value k (Pattern s) f j:=by
   have he:= (Packets.repack k (Pattern s) f hc h).tsum_eq; rw [tsum_fintype] at he
   unfold field; simp_rw [grid,cram]; exact he
lemma shove (s:Support n)(p:Finset ℕ) : Packets.selected (barcode A) (Pattern s) p ↔ (p:Set ℕ).PairwiseDisjoint (fun i=> (A.forced i).support) ∧ p.biUnion (fun i=>(A.forced i).inventory)=s:= marked_pattern _ _ p (fun i _=> (A.forced i).inventory_ne.mono (A.forced i).inventory_sup)
lemma shovel (f:ℕ→Poly B) (U:Config G n)(q:BudgetPoint)(p:Finset ℕ): Packets.value (barcode A) (Pattern (flags q.threshold U)) f p= if A.admissible q U p then ∏ i∈p,f i else 0:=by
   unfold Packets.value; split_ifs with hp he he; rfl; exact False.elim (he ((shove A _ p).1 hp));exact False.elim (hp ((shove A _ _).2 he));rfl
end YM.MergeProof.Accent
