import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Erosion
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Polar

/-!
# Replacing inputs everywhere on U

 Tests at a chosen B-dome. Survives even where profile calls intersect
 output flag halo. No changing a lookup WITHOUT paying for it (can split
 Mayor complements, but keep speck hat independently).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint
open Pulse Itinerary Raw Matter Scroll Vine Polar Frond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L n : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {x : Site c} {X : Coat T F} {l m : ℕ} {k : Finset ℕ} {R : Rep G f} {Z : Support c}
variable {w v : Air f G} {u b : Directions G f} {a : ℝ} {U V : Config G f}

/-- Pointwise synchronism. Can leave values large. Need BOTH sides agree at
    each protected Hot position and all cold near scopes. -/
structure Armor (X : Coat T F) (a : ℝ) (u : Directions G f) (U V : Config G f) : Prop where
  same : ∀ i, (¬ X.Hot i ∨ ‖u i‖≤4*a*X.t) → U i=V i
  pulse : 0<a*X.t
lemma unveils (X : Coat T F) (p : Room P S T X.x) (i : Site f) (he : AgreeNear S.ratio.parent (S.ratio.parent i) X.B U V) (R : Rep G f) :
    Contract.charges R k U i=Contract.charges R k V i := by
  have hf : 100≤X.B := p.sight.1
  have hk : i∈ RG.flags R.p.threshold U ↔ i∈ RG.flags R.p.threshold V := by
    rw [flags_spec,flags_spec]; refine exists_congr fun j => and_congr_right fun hj=> ?_
    rw [LocalRows.facesight _ (parent_step S) _ _ j (he.shrink (by have he:= Work.E01.sep_touched j i hj; rw [separation_comm] at he; have hq:= Work.E04.parent_separation S.ratio i j.1; omega))]
  unfold Contract.charges; simp_rw [hk]

namespace Armor
variable (H : Armor X a u U V)
include H
lemma heading (Y : Support c) (he : X.enforce (2*a) u (X.plaza Y)≠0) (i : Bond f) (hi : atEdge S i ∈Y) : U i=V i := by
  by_cases hp : X.Hot i
  · refine H.same _ (Or.inr ?_)
    have hf:i∈X.plaza Y := mem_filter.mpr ⟨mem_univ _,hp,Finset.not_disjoint_iff.mpr ⟨atEdge S i,hi,center_end _⟩⟩
    exact (X.protection _ (by rw [mul_assoc]; exact mul_pos (by norm_num) H.pulse) _ he i hf).trans_eq (by ring)
  exact H.same _ (Or.inl hp)
lemma venial (Y : Support f) (he : X.enforce (2*a) u (X.plaza (enlargement S.ratio 0 X.B Y)) ≠ 0) : Agrees Y U V :=
    fun i hi _=> H.heading _ he i (halo_subset _ _ (mem_image_of_mem S.ratio.parent hi))
lemma torrid (Y : Support f) (s : Signed) (he : X.enforce (2*a) u
    (X.plaza ((enlargement S.ratio 0 X.B Y).image (affine s 0)))≠0) : Agrees Y (pull s 0 U) (pull s 0 V) := by
  intro i hi hh
  have hx t (hf : t ∈ Y) : ∀ j : Bond f,j.1=s.act t → U j=V j := by
    intro j hj; apply H.heading _ he; unfold atEdge; rw [hj, S.ratio.parent_signed S.patch.odd_side,← affine0]; exact
      mem_image_of_mem _ (halo_subset _ _ (mem_image_of_mem _ hf))
  rw [Channel.charge,Channel.charge]; cases hp:s.flip i.2
  · rw [hx i.1 hi (Channel.edge s i) (by rw [positive s i hp])]
  rw [hx _ hh (Channel.edge s i) (by rw [negative s i hp])]

omit H in
lemma roots (X : Coat T F) (p : Room P S T X.x) {U V : Config G f} (s : Signed) (i : Spot c f)
    (he : AgreeNear S.ratio.parent (s.act (lead S i)) X.B U V) (t : Bool) : rootface X u U t s i=rootface X u V t s i := by
  let o:=lead S i; let k:=choice s X.k
  have hv:100≤X.B∧4*X.R+4+predReach S.patch ≤ X.B/100 := p.sight
  have hx : AgreeNear S.ratio.parent o (X.B/2+predReach S.patch) (pull s 0 U) (pull s 0 V) :=
    Zone.nearU S s (he.shrink (by change separation (s.act o) (s.act o)+_≤_; rw [separation_self]; omega))
  unfold rootface; apply congr_arg₂ (·-·) _ rfl
  apply rivers p i k k (fun _ _=>rfl) (hx.shrink (by change separation o o+X.B/2≤_; rw [separation_self]; omega))
  intro j hj; apply prediction_near_eq (funds_branch p.accepted)
  apply hx.shrink; change separation o j.1 ≤ X.B/2 at hj; omega

lemma motives (p : Room P S T X.x) (R : Rep G f) (i : Stream c f) : Polar.hover X a R u U i=Polar.hover X a R u V i := by
  unfold Polar.hover; dsimp only; by_cases hh : X.enforce (2*a) u (X.booth (rowSite S i))=0
  · simp_rw [hh,zero_mul]
  rw [roots X p i.1 i.2 (U:=U) (V:=V) (fun j hj=> H.heading (Animals.neighbors X.B _) hh j ((Animals.neighbors_mem ..).mpr hj)) true]

lemma uplinks (p : Room P S T X.x) (h : Intake P T X.x R) (i : LogLetter c f) :
    frost X a R u U i=frost X a R u V i := by
  unfold frost; by_cases he : X.enforce (2*a) u (X.plaza (space T 0 X.B R i))=0
  · rw [he,mul_zero,mul_zero]
  apply congrArg₂ (·*·) _ rfl
  have hp d (Z : ℕ→Atom G d) (t : Trans f) (ht : X.enforce (2*a) u (X.plaza (atomFoot S.ratio 0 X.B Z t)) ≠ 0) (y) :
      translateValue R.p Z y U t=translateValue R.p Z y V t := congrArg (y*·) (Raw.placed_local _ _ _ _ _ (H.torrid _ _ ht))
  rcases i with i|i|i|i|i|i <;> simp only [nest,Sum.elim]
  · exact congrArg Neg.neg (valueE R i (h.cap.labels.regular.smooth i) U V (H.venial _ he))
  · exact hp _ _ i he _
  · exact hp _ _ i he _
  · exact hp _ _ i he _
  · have hh t (hi : R.p.threshold * Real.exp ((t:ℕ)/R.clip.relaxation)<2) : t+2 ≤ X.B := by
      rw [h.received.2,h.received.3] at hi; exact le_trans (p.laneU t hi) (Nat.div_le_self ..)
    exact congrArg ((-orientation*R.beta)*·) (Raw.pair_local _ _ (till X.x) 1 _ _ _ X.B hh
      (pull i.1 0 U) (pull i.1 0 V) (H.torrid _ _ he))
lemma foreign (W : ℝ) (p : Room P S T X.x) (R : Rep G f) (k : Finset ℕ) (i : Panic c f) :
    flare X a R W u U k i= flare X a R W u V k i := by
  unfold flare; by_cases hh:X.enforce (2*a) u (X.plaza (halo X.B (districts S i)))=0
  · simp_rw [hh,zero_mul]
  suffices he:veil X R W U k i=veil X R W V k i by rw [he]
  let o:=focus_alarms S i
  have hp : AgreeNear S.ratio.parent o X.B U V := fun j hj=> H.heading _ hh j (halo_spec.mpr ⟨_,Coat.home_storm S i,hj⟩)
  have hz : 100≤X.B ∧ 4*X.R+4+predReach S.patch ≤ X.B/100 := p.sight
  unfold veil; rcases i with i|i|i|i|i
  · simp only [Sum.elim, Mask.fine,toll]; rw [LocalRows.facesight _ (parent_step S) U V i (hp.shrink
      (by change separation o o+4≤_; rw [separation_self]; omega))]
  · simp only [Sum.elim, Mask.noise, wire]; rw [prediction_near_eq (funds_branch p.accepted) U V X.k i (hp.shrink (by
      change separation o o+_≤_; rw [separation_self]; omega))]
  · exact (Emblems.choices U V _ _ X.k (funds_branch p.accepted) rfl rfl rfl
      (hp.shrink (by change separation o o+_≤_; rw [separation_self]; omega))).2.1
  · exact (Emblems.frames_agree U V i _ _ (funds_branch p.accepted) rfl (hp.shrink (by change separation o o+_≤_; rw [separation_self]; omega))).2
  exact unveils X p i hp R
end Armor
end YM.ConnectedActivityE6.Blaze
