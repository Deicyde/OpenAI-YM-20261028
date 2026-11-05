import YM.MergeProof.North.Fermi
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories Push Push.Local Motion
namespace Twin
variable {Z:Salt V G n} {t:ℝ}{b:Equiv.Perm V}{m:Motion}{x:Site n}{v u:V}
variable (h:Twin Z t m x v u b)
include h
lemma turf : ∃ e: Equiv.Perm Z.Turf, (∀ i,Focused v i.val.2 ↔ Focused u (e i).val.2) ∧ ∀ i,Focused v i.val.2 → (e i).val.1=sky m x i.val.1 ∧ (e i).val.2=drum b i.val.2:=by
    let r:= Equiv.prodCongr (sky m x) (drum b); let p:=fun i:Z.Turf=>Focused v i.val.2; let q:= fun i:Z.Turf=>Focused u i.val.2
    have hv(s:Support n)(i:(Aged V).Mode)(hp:Focused v i): (i.val.Nonempty ∧ i.val.image Z.grain⊆s) ↔ ((drum b i).val.Nonempty∧(drum b i).val.image Z.grain⊆ sky m x s):= and_congr (by rw [drum,pares,image_nonempty]) (h.homes i hp s)
    let f:{i//p i}→{i//q i}:=fun i=> ⟨⟨r i.val.val,(hv _ _ i.property).1 i.val.property⟩,(h.goes i.val.val.2).1 i.property⟩
    have ht: Bijective f:=by
       refine ⟨fun i j e=> Subtype.ext (Subtype.ext (r.injective (congr_arg (fun i=> i.val.val) e))), fun i=>?_⟩
       obtain ⟨s,hs⟩:= (sky m x).surjective i.val.val.1; obtain ⟨l,hl⟩:=(drum b).surjective i.val.val.2
       have he:r (s,l)=i.val.val:= Prod.ext hs hl
       have hh:Focused v l:= (h.goes l).2 (hl.symm ▸ i.property); exact ⟨⟨⟨(s,l),(hv s l hh).mpr (show ((r (s,l)).2.val.Nonempty∧(r (s,l)).2.val.image Z.grain⊆ (r (s,l)).1) from he.symm ▸ i.val.property)⟩,hh⟩,Subtype.ext (Subtype.ext he)⟩ -- bad he ▸
    obtain ⟨e,hv,hq⟩:=extends_on ht; refine ⟨e,hq,fun i hi=>?_⟩
    rw [show e i = (f ⟨i,hi⟩).val from hv ⟨i,hi⟩]; exact ⟨rfl,rfl⟩
lemma blade : ∃ e : Equiv.Perm Z.Brook, (∀ i,Focused v i.val.2 ↔ Focused u (e i).val.2) ∧ ∀ i,Focused v i.val.2 → (e i).val.1=puff m x i.val.1 ∧ (e i).val.2=drum b i.val.2:=by
    let r:= Equiv.prodCongr (puff m x) (drum b); let p:=fun i:Z.Brook=>Focused v i.val.2; let q:= fun i:Z.Brook=>Focused u i.val.2
    have hv(s:Box n)(i:(Aged V).Mode)(hp:Focused v i): (Sure s ∧ i.val.image Z.grain⊆s.1) ↔ (Sure (puff m x s) ∧ (drum b i).val.image Z.grain⊆ (puff m x s).1):= and_congr (by
       unfold Sure; change _ ↔ (sky m x _).Nonempty ∧ sky m x _⊆sky m x _; simp only [shading,image_nonempty,image_subset_image_iff (turnSites m.1 x).injective]) (h.homes i hp s.1)
    let f:{i//p i}→{i//q i}:=fun i=> ⟨⟨r i.val.val,(hv _ _ i.property).1 i.val.property⟩,(h.goes i.val.val.2).1 i.property⟩
    have ht: Bijective f:=by
       refine ⟨fun i j e=> Subtype.ext (Subtype.ext (r.injective (congr_arg (fun i=> i.val.val) e))), fun i=>?_⟩
       obtain ⟨s,hs⟩:= (puff m x).surjective i.val.val.1; obtain ⟨l,hl⟩:=(drum b).surjective i.val.val.2
       have he:r (s,l)=i.val.val:= Prod.ext hs hl
       have hh:Focused v l:= (h.goes l).2 (hl.symm ▸ i.property); exact ⟨⟨⟨(s,l),(hv s l hh).mpr (show Sure (r (s,l)).1 ∧ (r (s,l)).2.val.image Z.grain⊆ (r (s,l)).1.1 from he.symm ▸ i.val.property)⟩,hh⟩,Subtype.ext (Subtype.ext he)⟩
    obtain ⟨e,hv,hq⟩:=extends_on ht; refine ⟨e,hq,fun i hi=>?_⟩; rw [show e i = (f ⟨i,hi⟩).val from hv ⟨i,hi⟩]; exact ⟨rfl,rfl⟩
lemma perch : ∃ e : Equiv.Perm Z.Lawn, (∀ i,Focused v (Z.marker i) ↔ Focused u (Z.marker (e i)))∧ ∀ i,Focused v (Z.marker i) → Z.marker (e i)=drum b (Z.marker i) ∧ Z.leaf (e i)=sky m x (Z.leaf i) ∧ Z.syrup (e i)=stepUp m x (Z.syrup i):=by
    obtain ⟨e,hp,hE⟩:= h.turf
    let r:= Equiv.sumCongr (nome b) e; refine ⟨r,fun i=>?_,fun i hi=>?_⟩
    · rcases i with i|i
      · change Focused v ((Aged V).fire i) ↔ Focused u ((Aged V).fire (nome b i));rw [← go_one]; exact h.goes _
      exact hp i
    rcases i with ⟨i,j⟩|i
    · obtain rfl: i=v:= (which ..).1 hi; change (Aged V).fire (nome b _)=_ ∧ {Z.grain (b i,j)}= _ ∧ (fun _=>Z.pepper (b i,j))=_; rw [h.who]; refine ⟨(go_one b _).symm,?_,funext fun _=>h.debut _⟩
      rw [shading,h.ways]; exact (Finset.image_singleton ..).symm
    obtain ⟨hv,hz⟩:=hE i hi; refine ⟨hz,hv,funext fun U=>?_⟩
    change (Z.air _ U).part (e i).val.2=scalar m _; rw [hz]; change (Z.air (e i).val.1 U).part _= _; rw [hv]; exact h.kin _ hi _ _
end Twin
end YM.MergeProof.Ribbons
