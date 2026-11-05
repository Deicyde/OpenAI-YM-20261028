import YM.MergeProof.North.Gush
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush

/- generalized from YM.MergeProof.North.Ebb to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons.Deck
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Finset Function Marker Extra.Trajectories Accent BatchRibbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V] [DecidableEq I][DecidableEq J][Fintype V] {n:Side}{G:Gauge}{B:Census V}
variable (D:Deck V slot I J G n) (t:ℝ)(U:Config G n)(h:D.Wet t)
open MeasureTheory Set Ac Push.Local Push.GridApprox.Nil
-- quip quiet only on lone vac terms.
def Vaca (i:J) :Prop:=D.roster (.inr i)=∅
include h
lemma muted {p:D.Ink}(hp:(D.quip (.inr p)).val=∅): ∃ i:J,D.Vaca i∧p.val={Sum.inr i}:=by
   rw [D.paint] at hp; have hz (i)(hi:i∈p.val):D.roster i=∅:= Finset.eq_empty_of_forall_notMem (fun v hv=> notMem_empty v (hp ▸ mem_biUnion.mpr ⟨i,(show i∈ D.glyph (.inr p) from hi),hv⟩))
   obtain ⟨a,ha⟩:=p.property.wet; have hx:=mem_toRight.mp ha
   have he (j)(hj:j∈p.val): j=Sum.inr a:=by
      induction p.property.fire.2 _ hx j hj with
      | refl=> rfl
      | @tail k j _ hb ih=>
         have hk:=(ih hb.1); obtain ⟨h1,h2,z,h3,h4⟩:=hb; rw [hk] at h3; have hh:=hz _ h2
         cases z with
         | inl v=> exact False.elim (notMem_empty v (hz _ hx ▸ (show v∈D.roster (.inr a) from D.kiln.fuel_left.mp h3)))
         | inr v=>
           cases j with
           | inl b=> obtain ⟨c,hc⟩:= h.clean b; exact False.elim (notMem_empty c.1 (hh ▸ mem_image_of_mem _ hc))
           | inr b=>
             by_contra hn; have hA : v∈(D.spill a).1:= h.plain _ (hz _ hx) ▸ ((D.kiln.fuel_right).mp h3).2; have hB : v∈(D.spill b).1:= h.plain _ hh ▸ ((D.kiln.fuel_right).mp h4).2
             exact disjoint_left.mp (p.property.old ha (mem_toRight.mpr hj) fun e=> hn (congr_arg _ e.symm)) hA hB
   exact ⟨a,hz _ hx,eq_singleton_iff_unique_mem.mpr ⟨hx,he⟩⟩
lemma glass (i:J)(hi:D.Vaca i):D.roster (.inr i)=∅ ∧ D.mode_ (.inr i)=(Aged V slot).quiet:=by
   have hp : (D.mode_ (.inr i)).val=∅:= Finset.eq_empty_of_forall_notMem (fun ⟨v,b⟩ hv=> notMem_empty v ((show (span (D.mode_ (.inr i))).val=∅ from hi) ▸ mem_image_of_mem _ hv))
   exact ⟨hi,Subtype.ext hp⟩
lemma admits (i:J)(hi:D.Vaca i): D.Tank {Sum.inr i}:=by
    have hh:= (D.glass t h i hi).2
    refine { old:= (?_), buys:= fits_singleton _ _, ready:= ?_, fire:= ⟨singleton_nonempty _,fun a ha b hb=> by rw [mem_singleton.mp ha,mem_singleton.mp hb]; exact .refl⟩, wet:=⟨i,mem_toRight.mpr (mem_singleton_self _)⟩ }
    · have hp : toRight ({Sum.inr i}:Finset (I⊕J))={i}:=by ext; simp
      simp [hp]
    rw [worth_iff,combines, singleton_biUnion]; simp [ (show (span (D.mode_ (.inr i))).val=∅ from hi)]
lemma sends (p:D.Ink)(i:J)(hi:D.Vaca i)(hv:p.val={Sum.inr i}):
    D.fuse p.val=D.spill i ∧ D.quip (.inr p)=(Bud V).quiet ∧ D.nectar t U p=D.toll (.inr i) U:=by
    have he: D.reach p.val=(D.spill i).1:=by simp [reach,hv,h.plain i hi]
    have ha: D.stain p.val=(D.spill i).2:=by
       unfold stain; rw [show p.val.toRight={i} from (by rw [hv];ext; simp)]; simp
    refine ⟨by simp [fuse,he,ha],?_,?_⟩
    · apply Subtype.ext; rw [paint,(show D.glyph (.inr p)={Sum.inr i} from hv), singleton_biUnion]; exact hi
    unfold nectar; rw [he,ha]; split
    · unfold bud; rw [(show D.glyph (.inr p)={Sum.inr i} from hv)]; simp
    next hh=> exact (Classical.byContradiction (fun hu=> hh (h.allows i U hu))).symm

variable [Fintype I][Fintype J]
lemma sober (z:Box n):
    (cram (fun i:D.Ink=>D.fuse i.val) (fun i=>Poly.send (D.quip (.inr i)) (D.nectar t U i)) z).part (Bud V).quiet=
      (cram D.spill (fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) z).part (Aged V slot).quiet:=by
   let a:=fun i:D.Ink=> if D.fuse i.val=z then (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part (Bud V).quiet else 0
   let b:=fun i:J=>if D.spill i=z then (Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part (Aged V slot).quiet else 0
   let v:={i:J|D.Vaca i}; let f (i:v) : D.Ink:=⟨{Sum.inr i.val},D.admits _ h _ i.property⟩
   have hf: Injective f:= fun i j he=> Subtype.ext (Sum.inr.inj (Finset.singleton_inj.mp (congr_arg Subtype.val he)))
   have hv(i:v): a (f i)=b i.val:=by
      have hx:=D.sends t U h (f i) _ i.property rfl; unfold a b; rw [hx.1,hx.2.1,hx.2.2, (D.glass t h _ i.property).2]; simp [Poly.part_send]
   unfold cram; rw [Poly.share (hs:=Summable.of_finite),Poly.share (hs:=Summable.of_finite)];
   erw [_root_.tsum_subtype {i:D.Ink|D.fuse i.val=z} (fun i=> (Poly.send (D.quip (.inr i)) (D.nectar t U i)).part (Bud V).quiet),_root_.tsum_subtype {i:J|D.spill i=z} (fun i=>(Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)).part (Aged V slot).quiet)]
   suffices hp:(∑' i,a i)=∑' i,b i by simpa [a,b,indicator] using hp
   rw [← hf.tsum_eq (fun i hi=>?_)]
   · simp_rw [hv]; refine tsum_subtype_eq_of_support_subset (fun i (hi: i∈Function.support b)=>?_)
     change b i≠0 at hi; unfold b at hi; split at hi; swap; · contradiction
     rw [Poly.part_send] at hi; split at hi; next he=> unfold v; change (span (D.mode_ (.inr i))).val=∅; simp [← he,BatchRibbon.span,Census.quiet]
     contradiction
   change a i≠0 at hi; unfold a at hi; split at hi; swap; · contradiction
   rw [Poly.part_send] at hi; split at hi
   next he=> obtain ⟨i',hV,hZ⟩:= D.muted _ h (p:=i) (by rw [← he];rfl); exact ⟨⟨i',hV⟩,Subtype.ext hZ.symm⟩
   contradiction
end YM.MergeProof.BatchRibbons.Deck
