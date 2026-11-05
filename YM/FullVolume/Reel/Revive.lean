import YM.FullVolume.Reel.Treasure
/- Allocation restrictions. Asset carriers NEVER sum across volumes. bring transports to all allowed supports with silent poll. Masks full.-/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint.Tower Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof Marker Push Extra.Histories
variable {I J X E F:Type}[NormedAddCommGroup E][NormedSpace ℝ E][CompleteSpace E][NormedAddCommGroup F][NormedSpace ℝ F][CompleteSpace F]
variable {q t v s a:ℝ}{w:I→ℝ}{f g:sun→ I→ X→E}
-- extend by θ. payment independent all.So no linear dimension estimate hidden.
lemma Treasure.cape [Fintype I] [Fintype J](e:J→I) (he: Function.Injective e)(h: Treasure (w ∘ e) (fun i=> f i ∘ e) v)(hb:∀ i:sun,∀ j∉ Set.range e, f i j=0): Treasure w f v:=by
   obtain ⟨a,hA,hx⟩:= h.coins; let p:= Function.extend e a 0; have hp (x:J): p (e x)=a x:=he.extend_apply ..; have hu x (h:x∉ Set.range e): p x=0:= Function.extend_apply' _ _ _ h
   refine ⟨p,?_ ,fun j=>?_⟩
   · rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) ?_, Finset.sum_image he.injOn]; simp_rw [hp]; exact hA
     intro x _ hx; rw [hu x (fun ⟨y,hy⟩=> hx (mem_image.mpr ⟨_,mem_univ y,hy⟩)),mul_zero]
   by_cases he:j∈ Set.range e
   · obtain ⟨j,rfl⟩:= he; rw [hp]; exact hx _
   rw [hu j he]; simp_rw [fun i=>hb i j he]; exact Feel.staticC (fun _=>0) le_rfl (fun _=>norm_zero.le)
lemma Treasure.wide {B A : Set I}[Fintype A][Fintype B](he:A⊆B) (h : Treasure (fun i:↥A=> w i.val) (fun i=> f i ∘ Subtype.val) v)(hf:∀ i:sun,∀ x∉A, f i x=0): Treasure (fun i:↥B=>w i.val) (fun i=> f i ∘ Subtype.val) v:=by
    let g:↥A→↥B:= fun ⟨i,h⟩=>⟨i,he h⟩; exact Treasure.cape g (fun i j p=> Subtype.ext (congr_arg (fun v:↥B=>v.val) p)) h (fun i x he=> hf _ _ (fun h=>he ⟨⟨x.val,h⟩,rfl⟩))
end YM.FullVolume.Nectar
