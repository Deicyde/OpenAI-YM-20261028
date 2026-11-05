import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Growth
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical


/-!
# Rotate the copy, and the common-location ledgers

The rows themselves
still live in *their own* oriented coordinates (test Q derivative there;
don't rotate an already squared Q noise term by V and assume it matches).

Roots of selected affine rows in the common geometry are
`s.act (roots ... i)` for this window convention of SectorChange.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

lemma positive_site (s : Signed) (p : Site n) (i : Axis) (h : s.flip i = false) :
    s.act (p+step i)=s.act p+step (s.perm i) := by
  simpa only [affine,add_zero] using StepData.possite s 0 p i h
lemma negative_site (s : Signed) (p : Site n) (i : Axis) (h : s.flip i = true) :
    s.act (p+step i)=s.act p-step (s.perm i) := by
  simpa only [affine,add_zero] using StepData.negsite s 0 p i h
lemma positive_edge (s : Signed) (p : Site n) (i : Axis) (h : s.flip i = false) :
    sendEdge s 0 (p,i)=(s.act p,s.perm i) := by
  simp [sendEdge,Step.used,posDir,Step.rotate,h,affine]
lemma negative_edge (s : Signed) (p : Site n) (i : Axis) (h : s.flip i = true) :
    sendEdge s 0 (p,i)=(s.act (p+step i),s.perm i) := by
  rw [negative_site _ _ _ h]; simp [sendEdge,Step.used,posDir,Step.rotate,h,affine]

/-- Crossings of odd centered blocks, including the seam. -/
theorem replica_turn (g : Ratio c f) (hg : Odd g.count.val) (s : Signed) (V : Config G c) :
    replica g (pull s 0 V) = pull s 0 (replica g V) := by
  funext i
  obtain ⟨x,a⟩ := i
  rw [Motion.turn_read]
  cases hl : s.flip a
  · rw [positive_edge s _ _ hl]
    have hh : g.parent (s.act x+step (s.perm a)) = s.act (g.parent (x+step a)) := by
      rw [← positive_site s _ _ hl,g.parent_signed hg]
    unfold replica
    by_cases he : g.parent (x+step a) = g.parent x
    · simp [hh,g.parent_signed hg,he]
    have hne : s.act (g.parent (x+step a)) ≠ s.act (g.parent x) := fun h => he (s.act_injective h)
    simp only [he,hh,g.parent_signed hg,hne,Bool.false_eq_true,↓reduceIte]
    rw [Motion.turn_read,positive_edge s _ _ hl]; simp [hl]
  rw [negative_edge s _ _ hl]
  have hh : g.parent (s.act (x+step a)+step (s.perm a)) = s.act (g.parent x) := by
    rw [negative_site s _ _ hl,sub_add_cancel,g.parent_signed hg]
  have hh' : g.parent (s.act (x+step a)) = s.act (g.parent (x+step a)) := g.parent_signed hg _ _
  unfold replica
  by_cases he : g.parent (x+step a) = g.parent x
  · simp only [hh,hh',he,↓reduceIte,inv_one]
  have hp : g.parent (x+step a)=g.parent x+step a := by
    have h := g.parents_hop hg x a
    split at h <;> first | exact h | exact absurd h he
  have hne : s.act (g.parent x) ≠ s.act (g.parent (x+step a)) := fun h => he (s.act_injective h.symm)
  simp only [he,hh,hh',hne,↓reduceIte]
  rw [Motion.turn_read,negative_edge s _ _ hl]; simp [hl,hp]

/-- Typed incidence transfers on whole plaquette locations (not just the
positive base, which may shift). -/
theorem startPos_turn (s : Signed) (p : Cell f) :
    startPos S (Face.send s 0 p) = (startPos S p).image s.act := by
  unfold startPos
  rw [Work.H03.touched_send,Finset.image_image,Finset.image_image]
  simp only [Function.comp_def,affine,add_zero,S.ratio.parent_signed S.patch.odd_side]

theorem pinPos_turn (s : Signed) (b : Bond n) :
    pinPos (sendEdge s 0 b) = (pinPos b).image s.act := by
  obtain ⟨p,i⟩ := b
  cases he : s.flip i
  · rw [positive_edge s _ _ he]; simp [pinPos,positive_site s p i he]
  rw [negative_edge s _ _ he]; simp [pinPos,negative_site s p i he,Finset.pair_comm]

section members

lemma costs_turn (s : Signed) (A : Stores S) (p : Cell f) :
    p∈(turnStore s A).costs ↔ Face.send s 0 p∈A.costs := by
  change p∈A.costs.map (faces s f).symm.toEmbedding ↔ faces s f p ∈ A.costs
  simp
lemma aisle_turn (s : Signed) (A : Stores S) (i : Bond c) :
    i∈(turnStore s A).aisles ↔ sendEdge s 0 i∈A.aisles := by
  change i∈A.aisles.map (StepData.sendBonds s 0).symm.toEmbedding ↔ StepData.sendBonds s 0 i∈A.aisles
  simp
lemma flag_turn (s : Signed) (A : Stores S) (i : Site c) :
    i∈(turnStore s A).flags ↔ s.act i∈A.flags := by
  have he : StepData.sendSites s (0:Site c) i = s.act i := by change s.act i+0=_; rw [add_zero]
  rw [← he]; dsimp only [turnStore]; set e := StepData.sendSites s (0:Site c); simp

theorem place_turn (s : Signed) (A : Stores S) (i : Site c) :
    i∈(turnStore s A).place ↔ s.act i ∈ A.place := by
  simp only [place,Finset.mem_union,Finset.mem_biUnion,costs_turn,aisle_turn,flag_turn]
  refine or_congr (or_congr ?_ ?_) Iff.rfl
  · constructor
    · rintro ⟨p,hp,hi⟩; exact ⟨Face.send s 0 p,hp,startPos_turn s p ▸ Finset.mem_image_of_mem _ hi⟩
    rintro ⟨q,hq,hi⟩
    obtain ⟨p,hp⟩ := (faces s f).surjective q
    change Face.send s 0 p=q at hp; subst q
    rw [startPos_turn] at hi
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hi
    exact ⟨p,hq,s.act_injective he ▸ hb⟩
  constructor
  · rintro ⟨p,hp,hi⟩; exact ⟨sendEdge s 0 p,hp,pinPos_turn s p ▸ Finset.mem_image_of_mem _ hi⟩
  rintro ⟨q,hq,hi⟩
  obtain ⟨p,hp⟩ := (StepData.sendBonds s (0:Site c)).surjective q
  change sendEdge s 0 p=q at hp; subst q
  rw [pinPos_turn] at hi
  obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hi
  exact ⟨p,hq,s.act_injective he ▸ hb⟩

lemma dome_turn (s : Signed) (A : Stores S) (b : ℕ) (i : Site c) :
    i∈(turnStore s A).dome b ↔ s.act i∈A.dome b := by
  rw [dome,dome,halo_spec,halo_spec]
  constructor
  · rintro ⟨p,h,h'⟩; exact ⟨s.act p,(place_turn s A _).mp h,by rwa [separation_signed]⟩
  rintro ⟨q,h,h'⟩
  obtain ⟨p,rfl⟩ := s.actEquiv.surjective q
  refine ⟨p,(place_turn s A _).mpr h,?_⟩
  rwa [← separation_signed p i s]

end members

lemma frame_turn (h : S.patch.Branches S.kernel G) (U : Config G f) (k : S.Choices) (s : Signed) (i : Site c) :
    S.patch.frameMass S.kernel (expandAt (S.ratio.embed i) (pull s 0 U)) ((choice s k).1 i) =
      S.patch.frameMass S.kernel (expandAt (S.ratio.embed (s.act i)) U) (k.1 (s.act i)) := by
  have ht : ((S.withinChoice s (0:Site c)) (choice s k)) = k := by simp [choice]
  have he := S.port_site s (0:Site c) (choice s k).1 i
  have hb : (S.withinSites s (0:Site c)) (choice s k).1 = k.1 := congr_arg Prod.fst ht
  rw [expandAt_pull,(S.patch.frames_channel h s _ _).1]
  simp only [affine,add_zero] at *
  rw [S.ratio.signed,← he,hb]

end YM.AnalyticBridge.Annulus1AD
