import YM.MergeProof.North.Farr
import YM.OPE.Grouping.Family

/-!
# Copy coherence after arbitrary simultaneous grouping

Generalizes the one-reap Harmony proof in YM/MergeProof/North/Farr.lean;
output perms & budget in the remaining live polynomials. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.Fibers
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable {X₀ : Type*} [Fintype X₀][DecidableEq X₀] {Δ : Fibers X₀ V} {a₀:Equiv.Perm X₀}
open Extra.Histories Push Push.Local Motion
namespace CopyFamily
variable {Z:Salt V X₀ Δ G n} {t:ℝ}{b:Equiv.Perm V}{m:Motion}{x:Site n}{v u:Set V}
variable (h:CopyFamily Z t m x v u a₀ b)
include h
lemma turf : ∃ e: Equiv.Perm Z.Turf, (∀ i,Focus Δ v i.val.2 ↔ Focus Δ u (e i).val.2) ∧ ∀ i,Focus Δ v i.val.2 → (e i).val.1=sky m x i.val.1 ∧ (e i).val.2=pars a₀ i.val.2:=by
    let r:= Equiv.prodCongr (sky m x) (pars a₀); let p:=fun i:Z.Turf=>Focus Δ v i.val.2; let q:= fun i:Z.Turf=>Focus Δ u i.val.2
    have hv(s:Support n)(i:(Bud X₀).Mode)(hp:Focus Δ v i): (i.val.Nonempty ∧ i.val.image Z.grain⊆s) ↔ ((pars a₀ i).val.Nonempty∧(pars a₀ i).val.image Z.grain⊆ sky m x s):= and_congr (by rw [pares,image_nonempty]) (h.homes i hp s)
    let f:{i//p i}→{i//q i}:=fun i=> ⟨⟨r i.val.val,(hv _ _ i.property).1 i.val.property⟩,(h.goes i.val.val.2).1 i.property⟩
    have ht: Bijective f:=by
       refine ⟨fun i j e=> Subtype.ext (Subtype.ext (r.injective (congr_arg (fun i=> i.val.val) e))), fun i=>?_⟩
       obtain ⟨s,hs⟩:= (sky m x).surjective i.val.val.1; obtain ⟨l,hl⟩:=(pars a₀).surjective i.val.val.2
       have he:r (s,l)=i.val.val:= Prod.ext hs hl
       have hh:Focus Δ v l:= (h.goes l).2 (hl.symm ▸ i.property); exact ⟨⟨⟨(s,l),(hv s l hh).mpr (show ((r (s,l)).2.val.Nonempty∧(r (s,l)).2.val.image Z.grain⊆ (r (s,l)).1) from he.symm ▸ i.val.property)⟩,hh⟩,Subtype.ext (Subtype.ext he)⟩ -- bad he ▸
    obtain ⟨e,hv,hq⟩:=extends_on ht; refine ⟨e,hq,fun i hi=>?_⟩
    rw [show e i = (f ⟨i,hi⟩).val from hv ⟨i,hi⟩]; exact ⟨rfl,rfl⟩
lemma blade : ∃ e : Equiv.Perm Z.Brook, (∀ i,Focus Δ v i.val.2 ↔ Focus Δ u (e i).val.2) ∧ ∀ i,Focus Δ v i.val.2 → (e i).val.1=puff m x i.val.1 ∧ (e i).val.2=pars a₀ i.val.2:=by
    let r:= Equiv.prodCongr (puff m x) (pars a₀); let p:=fun i:Z.Brook=>Focus Δ v i.val.2; let q:= fun i:Z.Brook=>Focus Δ u i.val.2
    have hv(s:Box n)(i:(Bud X₀).Mode)(hp:Focus Δ v i): (Sure s ∧ i.val.image Z.grain⊆s.1) ↔ (Sure (puff m x s) ∧ (pars a₀ i).val.image Z.grain⊆ (puff m x s).1):= and_congr (by
       unfold Sure; change _ ↔ (sky m x _).Nonempty ∧ sky m x _⊆sky m x _; simp only [shading,image_nonempty,image_subset_image_iff (turnSites m.1 x).injective]) (h.homes i hp s.1)
    let f:{i//p i}→{i//q i}:=fun i=> ⟨⟨r i.val.val,(hv _ _ i.property).1 i.val.property⟩,(h.goes i.val.val.2).1 i.property⟩
    have ht: Bijective f:=by
       refine ⟨fun i j e=> Subtype.ext (Subtype.ext (r.injective (congr_arg (fun i=> i.val.val) e))), fun i=>?_⟩
       obtain ⟨s,hs⟩:= (puff m x).surjective i.val.val.1; obtain ⟨l,hl⟩:=(pars a₀).surjective i.val.val.2
       have he:r (s,l)=i.val.val:= Prod.ext hs hl
       have hh:Focus Δ v l:= (h.goes l).2 (hl.symm ▸ i.property); exact ⟨⟨⟨(s,l),(hv s l hh).mpr (show Sure (r (s,l)).1 ∧ (r (s,l)).2.val.image Z.grain⊆ (r (s,l)).1.1 from he.symm ▸ i.val.property)⟩,hh⟩,Subtype.ext (Subtype.ext he)⟩
    obtain ⟨e,hv,hq⟩:=extends_on ht; refine ⟨e,hq,fun i hi=>?_⟩; rw [show e i = (f ⟨i,hi⟩).val from hv ⟨i,hi⟩]; exact ⟨rfl,rfl⟩
lemma perch : ∃ e : Equiv.Perm Z.Lawn, (∀ i,Focus Δ v (Z.marker i) ↔ Focus Δ u (Z.marker (e i)))∧ ∀ i,Focus Δ v (Z.marker i) → Z.marker (e i)=pars a₀ (Z.marker i) ∧ Z.leaf (e i)=sky m x (Z.leaf i) ∧ Z.syrup (e i)=stepUp m x (Z.syrup i):=by
    obtain ⟨e,hp,hE⟩:= h.turf
    let r:= Equiv.sumCongr a₀ e; refine ⟨r,fun i=>?_,fun i hi=>?_⟩
    · rcases i with i|i
      · change Focus Δ v ((Bud X₀).fire i) ↔ Focus Δ u ((Bud X₀).fire (a₀ i));rw [Fibers.fires]; exact h.goes _
      exact hp i
    rcases i with i|i
    · have hu : Δ.bunch i ∈ v:= (focus_fire ..).1 hi
      change (Bud X₀).fire _=_ ∧ {Z.grain (a₀ i)}= _ ∧ (fun _=>Z.pepper (a₀ i))=_; refine ⟨fires _ _,?_,funext fun _=>h.debut _ hu⟩
      rw [shading,h.ways _ hu]; exact (Finset.image_singleton ..).symm
    obtain ⟨hv,hz⟩:=hE i hi; refine ⟨hz,hv,funext fun U=>?_⟩
    change (Z.air _ U).part (e i).val.2=scalar m _; rw [hz]; change (Z.air (e i).val.1 U).part _= _; rw [hv]; exact h.kin _ hi _ _
end CopyFamily
end YM.MergeProof.Ribbons.Fibers
