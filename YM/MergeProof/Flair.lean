import YM.MergeProof.Figure
import YM.MergeProof.Pitch
import YM.MergeProof.Tongue
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open Extra.Trajectories
variable (p:Support n)
structure Stars (i:Finset (Box n)):Prop where
    shines : ∀ j∈i, Sure j
    cash:i.Nonempty
    safe:(i:Set (Box n)).PairwiseDisjoint Prod.fst
    meets:∀ j∈i, ¬ Disjoint p j.1

def cluster (i:Finset (Box n)): Box n:= (p∪i.biUnion Prod.fst,i.biUnion Prod.snd)
variable (A:Activities G n)
local notation "f" => barcode A
lemma cluster_map (i:Finset ℕ): fusionBox A p i=cluster p (i.image (barcode A)):=by
   unfold cluster fusionBox; rw [image_biUnion,image_biUnion]; rfl
lemma surge (i:Finset ℕ) : Local.Packs A p i ↔ Stars p (i.image (barcode A)) ∧ (i:Set ℕ).InjOn (barcode A):=by
   have ht:= marked_pattern f (i.biUnion fun j=> (A.forced j).inventory) i (fun j _=> (A.forced j).inventory_ne.mono (A.forced j).inventory_sup)
   constructor
   · intro h; have hp:=(ht.2 ⟨h.separate,rfl⟩); refine ⟨⟨?_,h.nonempty.image f,hp.1.1,?_⟩,hp.2⟩
     · intro j hj; obtain ⟨k,_,rfl⟩:= mem_image.mp hj; exact ⟨(A.forced k).inventory_ne,(A.forced k).inventory_sup⟩
     intro j hj; obtain ⟨k,hk,rfl⟩:= mem_image.mp hj; exact h.hits _ hk
   rintro ⟨h,hp⟩; refine ⟨Finset.image_nonempty.mp h.cash,(ht.1 ⟨⟨h.safe,?_⟩,hp⟩).1,fun i hi=> h.meets _ (Finset.mem_image_of_mem _ hi)⟩; rw [image_biUnion]; rfl

variable (t:ℝ)(u:Box n)(U:Config G n)
def reflects (v : Finset (Box n)):= Stars p v ∧ cluster p v=u ∧ u.1∩flags t U=u.2
lemma den (i:Finset ℕ): Packets.selected (barcode A) (reflects p t u U) i↔ Local.Packs A p i∧ fusionBox A p i=u∧ u.1∩flags t U=u.2:=by unfold Packets.selected reflects; rw [surge, cluster_map]; tauto

def snap (v : Finset (Box n)):ℂ:= if reflects p t u U v then ∏ i∈v, profile A (fun j=> Complex.ofReal ∘ A.K j) i U else 0
-- infinite archives to finite SNAP
variable (B:Census V)
include B
lemma grain (h: Summable fun i=>(A.K i U)): portion A t p u U=∑ v,snap p A t u U v:=by
   let b:ℕ→ℂ:=fun i=>(↑(A.K i U):ℂ); let y(i:ℕ):Poly B:= Poly.send B.quiet (b i)
   let r:=reflects p t u U; let w(i:V):=(1:ℝ); have hw i:0<w i:=zero_lt_one
   have he:Summable fun i=> Poly.price w (y i):=by simp only [y,b,Poly.solo,Poly.quiet_toll,one_mul,Complex.norm_real]; exact h.norm
   let t':= Packets.value f r y; have hs:Summable t':=Packets.summable_value _ _ _ hw he
   have hy:= (Poly.budgeted hw he (fun i=>le_rfl)).1
   let g(i:Finset (Box n)):= if r i then ∏ j∈i, cram f y j else 0
   have hr:∑' i,t' i=∑ j,g j:= by
      have he:=(Packets.repack f r y hs hy).tsum_eq; rw [tsum_fintype] at he; exact he.symm
   have h0(i:Finset ℕ): grasp A t p i u U= (t' i).part B.quiet:=by
      unfold grasp t' Packets.value r; split_ifs with H H' H';
      · rw [shockProd₀]; refine Finset.prod_congr rfl fun i _=> ?_; unfold y; rw [Poly.part_send,if_pos rfl]
      · exact False.elim (H' ((den ..).2 H))
      · exact False.elim (H ((den ..).1 H'))
      rfl
   unfold portion; simp_rw [h0]; rw [← Poly.share hs,hr,Poly.part_sum]; refine Finset.sum_congr rfl (fun i _=>?_); unfold snap g; unfold r; split_ifs; -- r
   all_goals first|rfl|expose_names
   · rw [shockProd₀]; apply Finset.prod_congr rfl; intro j _; unfold cram profile; rw [Poly.share («f»:=fun i:{k//f k=j}=>y i.val) (hy.comp_injective Subtype.val_injective)]; apply tsum_congr; intro i; unfold y; rw [Poly.part_send,if_pos rfl] <;> rfl
   all_goals tauto
end YM.MergeProof.Accent
