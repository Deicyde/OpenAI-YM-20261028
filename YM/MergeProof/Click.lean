import YM.MergeProof.Stool
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Accent
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Push Marker Extra.Histories Ac
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {V I J Y : Type*}[DecidableEq V] {B:Census V} {G:Gauge}{n:Side}
open GridApprox.Nil Extra.Trajectories
variable (K:Box n → Config G n→Poly B)(u : J→Config G n→Poly B) (X:J→Support n)
variable (t:ℝ)(U:Config G n)
variable [DecidableEq J]
lemma turnout (p:Finset (Period X))(H:Packets.selected (forst X) (Pattern (flags t U)) p) : Parts (bloom X) (token X p)=p.image Subtype.val:=by
   unfold token; rw [← show (p.image Subtype.val).biUnion id=p.biUnion Subtype.val by rw [image_biUnion]; rfl]
   refine Ac.separates (bloom X) _ (fun i h=> ?_) (fun A ha B hB he => ?_)
   · obtain ⟨i,_,rfl⟩:=mem_image.mp h; exact i.property.spark
   obtain ⟨x,hx,rfl⟩:= mem_image.mp ha; obtain ⟨y,hy,rfl⟩:= mem_image.mp hB; exact (separateR X t U p H).1 hx hy fun hh=> he (congr_arg _ hh)
variable (hv:∀ i,K i U≠0 → Sure i) (hr:∀ i,u i U≠0→¬ Healthy t (X i) U)
include hv hr
lemma recoil (p:Finset (FlowKind J n)) (hp:paddle K u t U p≠0) :∃ j:Finset (Period X),Packets.selected (forst X) (Pattern (flags t U)) j ∧ token X j=p:=by
   let q:= Parts (bloom X) p
   have h := left_ne_zero_of_mul hp; unfold grid at h; split at h; swap; · contradiction
   rename_i he
   have hl(z : Box n)(hz:z∈p.toLeft) : Sure z:= hv z (fun hh=> h (prod_eq_zero hz hh))
   have hd(i:J)(hi:i∈p.toRight) : ¬ Healthy t (X i) U:= hr i (fun hh=> right_ne_zero_of_mul hp (prod_eq_zero hi hh))
   have hs (i:Finset _)(hh:i∈q) : Sealed X i:=by
      obtain ⟨hy,ha⟩:= Ac.lives (bloom X) p hh
      refine ⟨ha,?_,he.1.subset (coe_subset.mpr (toLeft_subset_toLeft hy)),?_⟩
      · obtain ⟨j,hj⟩:= ha.1; cases j with
        | inl j=> exact ⟨j,mem_toLeft.mpr hj⟩
        | inr j=>
          obtain ⟨x,hx,hf⟩:= Finset.not_disjoint_iff.mp (hd j (mem_toRight.mpr (hy hj))); rw [← he.2] at hf; obtain ⟨i,hi,hI⟩:=mem_biUnion.mp hf
          have hu:=mem_toLeft.mp hi; have ht: bonds (bloom X) p (.inr j) (.inl i):=⟨hy hj,hu,x,hx,(hl i hi).2 hI⟩
          exact ⟨i,mem_toLeft.mpr ((Ac.contains _ hh _ hj) ▸ ((Ac.bright _ _ _).2 ⟨hu,.single ht⟩))⟩
      rintro (j|j) hj; exact hl _ (mem_toLeft.mpr (hy hj)); obtain ⟨x,hx,-⟩:=Finset.not_disjoint_iff.mp (hd j (mem_toRight.mpr (hy hj))); exact ⟨x,hx⟩
   let j:= q.subtype (fun i=> Sealed X i); have hx:j.image Subtype.val=q:=by ext i; constructor; intro hi; obtain ⟨j,hj,rfl⟩:=mem_image.mp hi; exact mem_subtype.mp hj; intro hi; exact mem_image.mpr ⟨⟨i,hs i hi⟩, mem_subtype.mpr hi,rfl⟩ -- parser
   have hr : token X j=p:=by rw [token,← show (j.image Subtype.val).biUnion id=j.biUnion Subtype.val by rw [image_biUnion]; rfl, hx]; exact reconstruct ..
   refine ⟨j,(marked_pattern (forst X) _ _ (fun i _=> (moist X i).1.mono (moist X i).2)).2 ⟨fun i hi k hk hℓ=> ?_,?_⟩,hr⟩
   · exact Ac.separate (bloom X) p (mem_subtype.mp hi) (mem_subtype.mp hk) (fun e=> hℓ (Subtype.ext e))
   exact (net X j|>.symm).trans ((congr_arg (fun p:Finset (FlowKind J n)=>p.toLeft.biUnion Prod.snd) hr).trans he.2)
lemma allpoint : let Z(p):= Packets.value (forst X) (Pattern (flags t U)) (fun i=>crow K u X t i U) p; let W:= paddle K u t U
   ∑' p,Z p=∑' p,W p:=by
   intro Y W
   have hh (i : Function.support Y): Packets.selected (forst X) (Pattern (flags t U)) i.val := Classical.byContradiction (fun h=> i.property (if_neg h))
   have hu i (h:Packets.selected (forst X) (Pattern (flags t U)) i): W (token X i)=Y i:=(strung K u X t U i h).trans (if_pos h).symm
   let f (i : Function.support Y) : Function.support W:=⟨token X i.val,fun h=>i.property ((hu i.val (hh i)).symm.trans h)⟩
   have hp : Bijective f:=by
     refine ⟨fun i j he=>Subtype.ext (Finset.image_injective Subtype.val_injective ((turnout X t U i.val (hh i)).symm.trans ((congr_arg (fun i: Function.support W=> Parts (bloom X) i.val) he).trans (turnout X t U j.val (hh j))))),fun j=>?_⟩
     obtain ⟨i,h,H⟩:= recoil K u X t U hv hr j.val j.property; exact ⟨⟨i,fun e=> j.property ((show W j.val=W (token X i) from congr_arg W H.symm).trans ((hu i h).trans e))⟩,Subtype.ext H⟩
   let e:= Equiv.ofBijective f hp
   rw [← tsum_subtype_eq_of_support_subset (s:=Function.support Y) (f:=Y) Subset.rfl,← tsum_subtype_eq_of_support_subset (s:=Function.support W) (f:=W) Subset.rfl,← e.tsum_eq]; exact tsum_congr fun i=>(hu i.val (hh i)).symm
end YM.MergeProof.Accent
