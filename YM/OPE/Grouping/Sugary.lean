import YM.MergeProof.North.Sugary
import YM.OPE.Grouping.Fibers
import YM.OPE.Grouping.Gush

/-!
# Simultaneous collapses at a mesh scale

This accounting generalizes the proof for pairs in YM/MergeProof/North/Sugary.lean
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
open Collide
lemma ride (s:Finset (I⊕J))(hp:D.Ride s){p}(hv:p∈D.kiln.slabs s):D.Cove p:=by
   have hh:=(D.kiln.good hv).1; refine { old:=hp.old.subset (coe_subset.mpr (toRight_subset_toRight hh)), fire:=(D.kiln.good hv).2, buys:=Fits.subset D.mode_ hp.buys hh, ready:=?_ }
   rw [Fibers.worth_iff Δ]; intro i hi k hk; rw [Fibers.combines Δ] at hi; obtain ⟨j,hj,hI⟩:=mem_biUnion.mp hi; have hz:= (Fibers.worth_iff Δ _).mp hp.ready i ((Fibers.combines Δ hp.buys).symm ▸ mem_biUnion.mpr ⟨j,hh hj,hI⟩) k hk; obtain ⟨b,hb,hx⟩:= mem_biUnion.mp hz
   have hk: b∈p:= by rw [← Collide.owner _ hv j hj]; exact (Collide.aglow _).mpr ⟨hb, D.kiln.increases (i:=j) (.single ⟨hh hj,hb,i,hI,(Fibers.spans Δ _ i).2 ⟨k,hk,hx⟩⟩)⟩
   exact mem_biUnion.mpr ⟨b,hk,hx⟩
include h
lemma liquid (s:Finset (I⊕J))(hs:selected D.spill (Pattern (flags t U)) s.toRight)(hx:∀ i∈s,D.toll i U≠0){p}(hp:p∈D.kiln.slabs s)(ht:D.kiln.Takes p): p.toRight.Nonempty:=by
   obtain ⟨j|j,hj,H⟩:=ht; swap; exact ⟨j,mem_toRight.mpr hj⟩
   have ht:=(D.kiln.good hp).1 hj; have hY := h.resid j U H (hx _ ht)
   obtain ⟨x,hz,hx⟩:= not_disjoint_iff.mp hY
   obtain ⟨k,hk,hF⟩:=mem_biUnion.mp (((Accent.marked_pattern _ _ _ (fun i _=>D.footprint t h i)).mp hs).2.symm ▸ hx: x∈s.toRight.biUnion fun i=>(D.spill i).2) -- annotate
   have hK:=mem_toRight.mp hk
   have he: Sum.inr k∈p:= by
      rw [← Collide.owner _ hp (Sum.inl j) hj]; exact (Collide.aglow _).mpr ⟨hK, .single ⟨ht,hK,Sum.inr x,D.kiln.fuel_right.mpr ⟨D.kiln.opens H ht,hz⟩,D.kiln.fuel_right.mpr ⟨D.kiln.opens trivial hK,h.old _ ((h.sure k).2 hF)⟩⟩⟩
   exact ⟨k,mem_toRight.mpr he⟩
lemma charges (s:Finset (I⊕J))(hs:D.fee t U s≠0): ∃ p:Finset D.Quills,D.Pace t U p ∧ p.biUnion D.glyph=s:=by
   unfold fee Ribbons.item at hs; split at hs
   swap; · simp at hs
   next hv =>
   have hh:= (Accent.marked_pattern _ _ _ (fun i _=>D.footprint _ h i)).mp hv
   have hp:Fits D.mode_ s:=fits_of_tagged_prod _ (fun he=>hs (by rw [he,map_zero]))
   rw [tagged_prod _ s hp, Fibers.harvest] at hs; split at hs; swap; · contradiction
   next hk=>
   have hx(i)(hi:i∈s):D.toll i U≠0:=fun he=> hs (by rw [prod_eq_zero hi he,Poly.send_zero])
   let v:= D.kiln.slabs s; have he' (p:v):∃ i:D.Quills,D.glyph i=p.val:=by
        have he:=D.ride s ⟨hh.1,hp,hk⟩ p.property
        by_cases hf:D.kiln.Takes p.val
        · exact ⟨Sum.inr ⟨p.val,he,D.liquid t U h _ hv hx p.property hf⟩,rfl⟩
        exact ⟨Sum.inl ⟨p.val,he,hf⟩,rfl⟩
   choose f hf using he'; let S:= v.attach.image f; have he : S.image D.glyph=v:=by
      unfold S; rw [image_image]; rw [show (D.glyph ∘ f)=Subtype.val from funext hf,attach_image_val]
   have hk i (hi:i∈S): D.glyph i∈v:= he ▸ mem_image_of_mem _ hi
   have hb:S.biUnion D.glyph=s:=by rw [show S.biUnion D.glyph=(S.image D.glyph).biUnion id from (by symm; nth_rw 1 [image_biUnion]; rfl),he]; exact Collide.recombine _ _
   refine ⟨S, ⟨⟨fun i hi j hj hz=>?_,mem_univ _⟩, (Accent.marked_pattern _ _ _ (fun i _=>(D.hold _ h i).1.mono (D.hold _ h i).2)).mpr ⟨fun i hi j hj hz=>?_, (D.plume t h S).symm.trans ((congr_arg D.stain hb).trans hh.2)⟩⟩,hb⟩
   · change Disjoint (D.quip i).val (D.quip j).val; rw [D.paint,D.paint]; exact D.kiln.clubs_away s (hk _ hi) (hk _ hj) (fun e=> hz (D.tale e))
   exact D.kiln.walls_away _ (mem_filter.mpr ⟨hk _ (mem_toRight.mp hi),D.blot _ i.property.wet⟩ : i.val∈v.filter D.kiln.Takes) (mem_filter.mpr ⟨hk _ (mem_toRight.mp hj),D.blot _ j.property.wet⟩ : j.val∈v.filter D.kiln.Takes) (fun e=> hz (Subtype.ext e))
lemma needs {s:Finset D.Quills}(hs:D.value t U s≠0):D.Pace t U s:=by
   unfold value Ribbons.item at hs; split at hs
   next he=> exact ⟨fits_of_tagged_prod _ hs,he⟩
   next=> contradiction
lemma measured (i:D.Paper):(D.quip (Sum.inl i)).val.Nonempty:=by
   rw [paint]; obtain ⟨j|j,hj⟩:= i.property.fire.1
   · obtain ⟨b,he⟩:=h.clean j; exact ⟨Δ.bunch b,mem_biUnion.mpr ⟨_,(show Sum.inl j∈D.glyph (.inl i) from hj),mem_image_of_mem Δ.bunch he⟩⟩
   exact False.elim (i.property.dry ⟨_,hj,trivial⟩)
variable [Fintype I][Fintype J]
lemma bookBind : Fibers.reap Δ (Poly.pass (∑ i:I,Poly.send (D.mode_ (.inl i)) (D.toll (.inl i) U)) * field (cram D.spill fun i=>Poly.send (D.mode_ (.inr i)) (D.toll (.inr i) U)) (flags t U))=
      Poly.pass (∑ i:D.Paper, Poly.send (D.quip (.inl i)) (D.bud U (.inl i))) * field (cram (fun i:D.Ink=>D.fuse i.val) fun i=>Poly.send (D.quip (.inr i)) (D.nectar t U i)) (flags t U):=by
   rw [expansion D.mode_ D.spill (flags t U) (fun i=> D.toll i U) h.clean,map_sum]
   change ∑ s,D.fee t U s= Poly.pass (∑ i:D.Paper,Poly.send (D.quip (.inl i)) (D.sap t U (.inl i))) * field (cram (fun i:D.Ink=>D.fuse i.val) fun i=>Poly.send (D.quip (.inr i)) (D.sap t U (.inr i))) _
   rw [expansion _ _ _ _ (D.measured t h)];
   let Z:=D.value t U; let Q:= D.fee t U
   let f : Function.support Z→Function.support Q:=fun s=> ⟨s.val.biUnion D.glyph, fun H=> s.property ((D.billed _ _ h _ (D.needs t U h s.property)).symm.trans H)⟩
   have hi: Injective f:=by
      intro x y he; apply Subtype.ext; apply image_injective D.tale
      rw [← D.repair _ _ h x.val (D.needs t U h x.property),← D.repair _ _ h y.val (D.needs t U h y.property), (show x.val.biUnion _ = y.val.biUnion _ from congr_arg Subtype.val he)]
   have hp : Surjective f:=by
      intro y; obtain ⟨s,he,hp⟩:=D.charges _ _ h _ y.property; exact ⟨⟨s,fun hz=> y.property (hp ▸ (D.billed _ _ h s he).trans hz)⟩,Subtype.ext hp⟩
   have H := (((Equiv.ofBijective f ⟨hi,hp⟩).hasSum_iff_of_support (fun s=>D.billed t U h _ (D.needs _ _ h s.property))).mp (Summable.of_finite.hasSum (f:=Z))).tsum_eq
   rw [tsum_fintype,tsum_fintype] at H; exact H
end YM.MergeProof.Ribbons.Fibers.Deck
