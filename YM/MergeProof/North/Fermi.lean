import YM.MergeProof.North.Stator
import YM.MergeProof.Weathervane

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons
open Finset Function Marker Extra.Trajectories Accent Ribbon Packets Lattice Wilson RG Further.ShellBirth49.Fusing
open scoped Topology BigOperators Classical
variable {V I J : Type*} [DecidableEq V][Fintype V] {n:Side}{G:Gauge}{B:Census V}
open Extra.Histories Push Push.Local Motion
variable (b: Equiv.Perm V)
def nome : Equiv.Perm (Name V):= Equiv.prodCongr b (Equiv.refl _)
def pars (B:Equiv.Perm V):Equiv.Perm (Bud V).Mode where
    toFun p:=⟨p.val.image B,mem_univ _⟩
    invFun p:=⟨p.val.image B.symm,mem_univ _⟩
    left_inv p:=Subtype.ext (by simp [image_image])
    right_inv p:=Subtype.ext (by simp [image_image])
lemma pares (i:(Bud V).Mode): (pars b i).val=i.val.image b:=rfl
def drum := pars (nome b)
lemma recall (i:(Aged V).Mode): span (drum b i)=pars b (span i):=Subtype.ext (by unfold span; simp only [drum,pares,image_image];rfl)
lemma garner (j:(Aged V).Mode):Ribbon.Pays j↔ Ribbon.Pays (drum b j):=by
    have he (i:(Bud V).Mode): plena (pars b i)=drum b (plena i):=by
       apply Subtype.ext; ext ⟨x,y⟩; rw [drum, pares]; change (x,y) ∈ _×ˢ univ↔ _ ; rw [mem_product,pares]; constructor
       · intro h; obtain ⟨i,hi,rfl⟩:= mem_image.mp h.1; exact mem_image.mpr ⟨(i,y),mem_product.mpr ⟨hi,mem_univ _⟩,rfl⟩
       intro h; obtain ⟨⟨i,c⟩,hj,hv⟩:=mem_image.mp h; exact ⟨mem_image.mpr ⟨i,(mem_product.mp hj).1,Prod.mk.inj hv|>.1⟩,mem_univ _⟩
    unfold Ribbon.Pays; rw [recall,he,(drum b).apply_eq_iff_eq]

def Focused (v:V)(p:(Aged V).Mode):Prop:= (span p).val⊆ {v}
lemma going (v:V)(p:(Aged V).Mode): Focused v p ↔ Focused (b v) (drum b p):=by
    unfold Focused; rw [recall,pares,← image_singleton b]; exact (Finset.image_subset_image_iff b.injective).symm
lemma go_one (p:Name V) : drum b ((Aged V).fire p)=(Aged V).fire (nome b p):= Subtype.ext (by unfold drum; rw [pares];exact image_singleton ..)
lemma which (v:V)(p:Name V):Focused v ((Aged V).fire p) ↔ p.1=v:=by simp [Focused,Census.fire,span]

variable (Z: Salt V G n)
structure Twin (z : ℝ) (m:Motion)(x:Site n)(v u:V) (b:Equiv.Perm V) : Prop where
   who : b v=u
   ways i : Z.grain (u,i) = affine m.1 x (Z.grain (v,i))
   debut i: Z.pepper (u,i)= scalar m (Z.pepper (v,i))
   kin p (hp:Focused v p) i U: (Z.air (MergeProof.sky m x i) U).part (drum b p)=scalar m ((Z.air i (pull m.1 x U)).part p)
   jets p (hp:Focused v p) i U:(Z.river (puff m x i) U).part (drum b p)= scalar m ((Z.river i (pull m.1 x U)).part p)
variable {t:ℝ}{m: Motion}{x:Site n}{v u:V}
local notation "E"=> Equiv.Perm
lemma extends_on [Fintype I]{p q : I→Prop}{f:{i//p i}→{i// q i}}(he:Bijective f) : ∃ k:E I,(∀ i:{i//p i}, k i.val=(f i).val) ∧ ∀ i,p i ↔ q (k i):=by
    let B:= Equiv.ofBijective f he; refine ⟨Equiv.extendSubtype B,fun i=> Equiv.extendSubtype_apply_of_mem B i.val i.property,fun i=>⟨fun hi=>Equiv.extendSubtype_mem B i hi,fun hi=> not_not.mp (fun he=> Equiv.extendSubtype_not_mem B i he hi)⟩⟩
namespace Twin
variable {Z b}
variable (h:Twin Z t m x v u b)
include h
lemma goes (i:(Aged V).Mode) : Focused v i↔ Focused u (drum b i):=by rw [←h.who]; exact going ..
lemma homes (i:(Aged V).Mode)(hp:Focused v i)(p:Support n) : i.val.image Z.grain⊆ p↔ (drum b i).val.image Z.grain ⊆ sky m x p:=by
   have he:(drum b i).val.image Z.grain=(i.val.image Z.grain).image (turnSites m.1 x):=by
      unfold drum; rw [pares,image_image,image_image]; apply Finset.image_congr; rintro ⟨k,j⟩ hj; have hh : k=v:=mem_singleton.mp (hp (mem_image_of_mem _ hj)); subst k; change Z.grain (b _,_)=_; rw [h.who]; exact h.ways _
   rw [he,shading]; exact (Finset.image_subset_image_iff (turnSites m.1 x).injective).symm
lemma kilo (i:(Aged V).Mode)(hp:Focused v i)(p:Support n): Z.kiln (sky m x p) (drum b i)=sky m x (Z.kiln p i):=by
    unfold Salt.kiln; rw [recall,pares,shading,shading,image_union,image_image,image_image]; refine congr_arg (_ ∪ ·) (Finset.image_congr ?_); intro i hi; rw [show i=v from mem_singleton.mp (hp hi)]; dsimp only [Function.comp]; rw [h.who]; exact h.ways _
end Twin
end YM.MergeProof.Ribbons
