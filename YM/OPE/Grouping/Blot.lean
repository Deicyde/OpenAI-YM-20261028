import YM.MergeProof.North.Blot
import YM.OPE.Grouping.Family
import YM.OPE.Grouping.Billow

/-!
# Copy coherence after arbitrary simultaneous grouping

Generalizes the one-reap Harmony proof in YM/MergeProof/North/Blot.lean;
output perms & budget in the remaining live polynomials. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers.CopyFamily
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
open Extra.Histories Push Push.Local Motion Equiv
variable {V I J : Type*}[DecidableEq I][DecidableEq J] [DecidableEq V][Fintype V]{G:Gauge}{n:Side}
variable {X₀ : Type*} [Fintype X₀][DecidableEq X₀] {Δ : Fibers X₀ V} {a₀:Equiv.Perm X₀}
variable {D:Deck V X₀ Δ I J G n}{E:Equiv.Perm I}{F:Equiv.Perm J}{b:Equiv.Perm V}{v u:Set V}{m:Motion}{x:Site n}(h:Glow D E F v u m x b a₀)
local notation "P!"=> Equiv.sumCongr E F
set_option quotPrecheck false
variable {s:Finset (I⊕J)}(ht:∀ i∈s,Focus Δ v (D.mode_ i))
include h ht
namespace Glow
lemma license : Fits D.mode_ s ↔ Fits D.mode_ (s.image (P!)):=by
   have he:= Ribbons.Twin.dist (f:=fun i=> (D.mode_ i).val) (f':=fun i=> (D.mode_ i).val) (R:=I) (P!) s Disjoint Disjoint (fun i hi j hj=>by
       rw [(h.paint _ (ht _ hi)).1,(h.paint _ (ht _ hj)).1,pares,pares]; exact (Finset.disjoint_image (a₀).injective).symm)
   exact ⟨fun hh=>⟨he.mp hh.1,mem_univ _⟩,fun hh=> ⟨he.mpr hh.1,mem_univ _⟩⟩
lemma enters (he:Fits D.mode_ s) : unionTag _ _ ((h.license ht).1 he)=pars a₀ (unionTag _ _ he):=by
   apply Subtype.ext; simp only [pares,unionTag,Finset.image_biUnion,biUnion_image] -- inspect
   exact biUnion_congr rfl (fun i hi=> congr_arg Subtype.val (h.paint _ (ht _ hi)).1)
lemma trip : D.Ride s↔ D.Ride (s.image (P!)):=by
    have hh : (s.toRight:Set J).PairwiseDisjoint (fun i=> (D.spill i).1)↔ (↑(s.image (P!)).toRight:Set J).PairwiseDisjoint (fun i=> (D.spill i).1):=by
       rw [Ribbons.Twin.Glow.shores]; refine Ribbons.Twin.dist (R:=I) F s.toRight (f:=fun i=> (D.spill i).1) (f':=fun i=>(D.spill i).1) Disjoint Disjoint ?_
       intro i hi j hj; rw [h.flood _ (ht _ (mem_toRight.mp hi)),h.flood _ (ht _ (mem_toRight.mp hj))]; exact (meet_sky m x ..).symm
    have hz:= h.license ht
    constructor
    · intro hp; refine ⟨hh.mp hp.old,hz.mp hp.buys,?_⟩
      rw [h.enters ht hp.buys]; exact (h.permutes.garner _).mp hp.ready
    intro hp; refine ⟨hh.mpr hp.old,hz.mpr hp.buys,?_⟩; exact (h.permutes.garner _).mpr (h.enters ht (hz.mpr hp.buys) ▸ hp.ready)
omit ht in
lemma chars (i:I⊕J)(hi:Focus Δ v (D.mode_ i)): D.kiln.dirty ((P!) i)↔ D.kiln.dirty i:=by
    cases i; exact (h.hot _ hi).symm; exact Iff.rfl
lemma passes : D.Cove s↔ D.Cove (s.image (P!)):=by
    have hk:= Kilner.molecule D.kiln (P!) b (turnSites m.1 x) s (fun i hi=>⟨?_,(h.paint _ (ht _ hi)).2.1.trans (shading ..),h.chars _ (ht _ hi)⟩)
    · exact ⟨fun hh=>⟨(h.trip ht).1 hh.toRide,hk.1 hh.fire⟩,fun hh=> ⟨(h.trip ht).2 hh.toRide,hk.2 hh.fire⟩⟩
    change (Δ.span _).val=(Δ.span _).val.image b; rw [(h.paint _ (ht _ hi)).1,h.permutes.recalls,pares]
lemma soaked: D.kiln.Takes s↔ D.kiln.Takes (s.image (P!)):=by
    constructor
    · rintro ⟨i,hi,hg⟩; exact ⟨_,mem_image_of_mem (P!) hi,(h.chars _ (ht _ hi)).2 hg⟩
    rintro ⟨i,hi,hg⟩; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact ⟨j,hj,(h.chars _ (ht _ hj)).1 hg⟩
lemma whisk: D.Comb s↔ D.Comb (s.image (P!)):=by
    have hz:=not_congr (h.soaked ht); exact ⟨fun g=>⟨(h.passes ht).1 g.toCove,hz.1 g.dry⟩,fun g=>⟨(h.passes ht).2 g.toCove,hz.2 g.dry⟩⟩
lemma sink: D.Tank s↔ D.Tank (s.image (P!)):=by
    have hz : (s.image (P!)).toRight.Nonempty↔s.toRight.Nonempty:=by rw [Ribbons.Twin.Glow.shores,image_nonempty];
    exact ⟨fun g=>⟨(h.passes ht).1 g.toCove,hz.2 g.wet⟩,fun g=>⟨(h.passes ht).2 g.toCove,hz.1 g.wet⟩⟩
end Glow
end YM.MergeProof.Ribbons.Fibers.CopyFamily
