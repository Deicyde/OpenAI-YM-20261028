import YM.MergeProof.North.Stained
import YM.OPE.Grouping.Fibers
import YM.OPE.Grouping.Sugary

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/Stained.lean
to a projection along fibers. The Deck prices a nonempty finite number of children
(not necessarily common across grouping regions).
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers.Deck
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [DecidableEq I][DecidableEq J][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {S₀ : Type*} [Fintype S₀][DecidableEq S₀] {Δ : Fibers S₀ V}
variable (D:Deck V S₀ Δ I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)
open MeasureTheory Ac Push.GridApprox.Nil Push
structure Smooth (t:ℝ):Prop where
   home i : UsesFinal t (D.cover i) (D.toll i)
   bear i : Measurable (D.toll i)
   rot i : GaugeInvariant (D.toll i)
   allows i U : ¬ D.ash i→ D.toll (.inl i) U≠0 → Healthy t (D.cover (.inl i)) U
variable [Fintype I][Fintype J]
def leaf (i:D.Quills)(U:Config G n):=Poly.send (D.quip i) (D.sap t U i)
def sky : Support n→ Config G n→ Poly (Bud V):= tally (fun i:D.Paper=> D.reach i.val) (D.leaf t ∘ Sum.inl)
def clay : Box n→ Config G n→ Poly (Bud V):= tally (fun i:D.Ink=>D.fuse i.val) (D.leaf t ∘ Sum.inr)
variable (hr:D.Smooth t)
include hr h
lemma lucid (i:D.Quills) : Borne D.seat (D.reach (D.glyph i)) (D.leaf t i) t:=by
    let z:= D.reach (D.glyph i); have hu:UsesFinal t z (fun U=>D.bud U i):= fun U V hx hp=> prod_congr rfl (fun j hj=> Work.H03.reads_larger (subset_biUnion_of_mem _ hj) (hr.home j) U V hx hp)
    have he : GaugeInvariant fun U=> D.bud U i:= fun s U=> prod_congr rfl (fun j _=> hr.rot j s U)
    have hp : Measurable fun U=> D.bud U i:= Finset.measurable_fun_prod _ fun j _=> hr.bear j
    refine ⟨fun U V h1 h2=>congr_arg (Poly.send (D.quip i)) ?_,fun s U=>congr_arg (Poly.send (D.quip i)) ?_,fun j=> ?_, fun U=> scope_send _ _ _ ?_⟩ -- check
    · cases i
      next=> exact hu U V h1 h2
      next i=> change D.nectar t U i=D.nectar t V i; unfold nectar; rw [show D.reach i.val∩flags t U=_ from h2, show D.bud U _= D.bud V (.inr i) from hu U V h1 h2]; rfl
    · cases i
      next=> exact he s U
      next i=> change D.nectar t _ i=D.nectar t U i; rw [nectar,gauge_flags,(show D.bud _ _=D.bud U (.inr i) from he s U)]; rfl
    · simp only [leaf,Poly.part_send]; split; swap; · exact measurable_const
      cases i with
      | inl i=> exact hp
      | inr i=> change Measurable fun U=>D.nectar t U i; exact Measurable.ite (census_me _ _ _) hp measurable_const
    intro j hj; change j∈(D.quip i).val at hj; rw [paint] at hj; obtain ⟨a,ha,hx⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨a,ha,h.buys _ _ hx⟩
lemma clearBurn (j:Support n) : Burns D.seat j (D.sky t j) t:=by
    apply transitE (fun i:D.Paper=> D.reach i.val) (r:=id) (he:=fun _=>Summable.of_finite)
    intro i; refine ⟨D.lucid _ h hr (.inl i),fun U hv=> ?_,fun U=> (Poly.part_send ..).trans (if_neg (fun he=> (D.measured _ h i).ne_empty (congr_arg Subtype.val he.symm)))⟩
    have hx:D.bud U (.inl i)≠0:=fun he=>hv (by change Poly.send _ (D.bud U (.inl i))=_; rw [he,Poly.send_zero])
    exact (disjoint_biUnion_left _ _ _).mpr (fun b hb=>by
      cases b
      next b => exact hr.allows b U (fun he=> i.property.dry ⟨_,hb,he⟩) (fun h=> hx (prod_eq_zero hb h))
      next b=> exact False.elim (i.property.dry ⟨_,hb,trivial⟩))
lemma cloudy (j:Box n): Flow D.seat j (D.clay t j) t:=by
    apply transitK (fun i:D.Ink=>D.fuse i.val) (r:=id) (he:=fun _=>Summable.of_finite)
    intro i; refine ⟨D.lucid _ h hr (.inr i),fun U hv=> ⟨?_,D.hold t h i⟩⟩ -- typo
    by_contra hn; exact hv (by change Poly.send _ (D.nectar t U i)=_; unfold nectar; rw [if_neg (show ¬ D.reach i.val ∩ flags t U=D.stain i.val from hn),Poly.send_zero])

omit hr
lemma startOld : Fibers.reap Δ (Poly.pass (∑ i:I,Poly.send (D.mode_ (.inl i)) (D.toll (.inl i) U)) * field (cram D.spill fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) (flags t U))=
         Poly.pass (∑ i: Support n,D.sky t i U)*field (fun i=>D.clay t i U) (flags t U):=by
    rw [bookBind _ _ _ h]; congr 2 -- inspect
    let f:=fun i:D.Paper=> D.leaf t (.inl i) U
    have he:= (border (p:=f) (fun i:D.Paper=>D.reach i.val) Summable.of_finite).tsum_eq
    rw [tsum_fintype,tsum_fintype] at he
    exact he.symm
end YM.MergeProof.Ribbons.Fibers.Deck
