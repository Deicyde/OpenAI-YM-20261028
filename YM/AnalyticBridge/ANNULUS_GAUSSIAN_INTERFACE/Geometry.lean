import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion
import YM.SectorNext.LARGE_FIELD_REMAINDERS.CorePacket


set_option warningAsError false

/-!
# Geometry comparing the two annulus data at one sector

Use the actual SectorChange conventions ( with the endpoint-pair
convention), not a translation-invariant or continuum inverse. All periods
are actual tori. A payment for a merged packet O of A will have hypotheses
*with* buffers; the part of the proof purely about counting anchors also
works with overlapped/wrapping buffers. Coincident seeds are not
identified. Keep the orientation of *both* endpoints, including at flags.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Annulus
open Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree
  YM.Push.SectorMeasure Oriented Exterior Bloch Next.SectorChange
open YM.SectorNext.Remainder (outside_dome)
open YM.SectorNext.Remainder.Affine
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n : Side} {S : StepData c f}

section turns
variable (s : Signed)

lemma step_negative (i : Axis) (hs : s.flip i = true) (v : Site n) :
    s.act (v+step i) = s.act v-step (s.perm i) := by
  have he := StepData.negsite s (0:Site n) v i hs
  simpa only [affine,add_zero] using he

lemma step_positive (i : Axis) (hs : s.flip i = false) (v : Site n) :
    s.act (v+step i) = s.act v+step (s.perm i) := by
  have he := StepData.possite s (0:Site n) v i hs
  simpa only [affine,add_zero] using he

lemma edge_positive (b : Bond n) (h : s.flip b.2 = false) :
    sendEdge s 0 b = (s.act b.1,s.perm b.2) := by simp [sendEdge,Step.rotate,posDir,Step.used,h,affine]
lemma edge_negative (b : Bond n) (h : s.flip b.2 = true) :
    sendEdge s 0 b = (s.act b.1-step (s.perm b.2),s.perm b.2) := by simp [sendEdge,Step.rotate,posDir,Step.used,h,affine]
lemma pin_send (b : Bond n) : pinPos (sendEdge s 0 b)=(pinPos b).image s.act := by
  cases he : s.flip b.2
  · rw [edge_positive s _ he]; simp [pinPos,step_positive s _ he]
  · rw [edge_negative s _ he]; simp [pinPos,step_negative s _ he,Finset.pair_comm]
lemma start_send (p : Cell f) : startPos S (faces s f p)=(startPos S p).image s.act := by
  unfold startPos; change (touched (Face.send s 0 p)).image S.ratio.parent=_
  simp only [Work.H03.touched_send,Finset.image_image,Function.comp_def,affine,add_zero,S.ratio.parent_signed S.patch.odd_side]
lemma turn_costs (A : Stores S) (p : Cell f) : p ∈ (turnStore s A).costs ↔ faces s f p ∈ A.costs := by
  simp [turnStore]
lemma turn_aisles (A : Stores S) (b : Bond c) : b ∈ (turnStore s A).aisles ↔ sendEdge s 0 b ∈ A.aisles := by
  change _ ↔ StepData.sendBonds s 0 b ∈ _
  simp [turnStore]
lemma turn_flags (A : Stores S) (i : Site c) : i ∈ (turnStore s A).flags ↔ s.act i ∈ A.flags := by
  have he : StepData.sendSites s 0 i = s.act i := add_zero _
  rw [← he]
  let e := StepData.sendSites s (0:Site c)
  change i∈A.flags.map e.symm.toEmbedding ↔ e i∈A.flags
  rw [Finset.mem_map]; constructor
  · rintro ⟨x,hx,rfl⟩; simpa only [Equiv.toEmbedding_apply,e.apply_symm_apply]
  · intro ha; exact ⟨_,ha,e.symm_apply_apply i⟩

private lemma turn_image (X : Finset (Site n)) (x : Site n) : s.act x ∈ X.image s.act ↔ x∈X := by
  constructor
  · intro h; obtain ⟨a,ha,he⟩ := Finset.mem_image.mp h; exact s.act_injective he ▸ ha
  exact Finset.mem_image_of_mem _

lemma turn_place (A : Stores S) (x : Site c) : x∈(turnStore s A).place ↔ s.act x∈A.place := by
  simp only [place,Finset.mem_union,Finset.mem_biUnion]
  apply or_congr _ (turn_flags ..); apply or_congr
  · constructor
    · rintro ⟨p,hp,hx⟩; refine ⟨_,(turn_costs ..).mp hp,?_⟩; rw [start_send]; exact (turn_image ..).mpr hx
    · rintro ⟨p,hp,hx⟩; obtain ⟨p,rfl⟩ := (faces s f).surjective p
      rw [start_send,turn_image] at hx; exact ⟨p,(turn_costs ..).mpr hp,hx⟩
  · constructor
    · rintro ⟨p,hp,hx⟩; refine ⟨_,(turn_aisles ..).mp hp,?_⟩; rw [pin_send]; exact (turn_image ..).mpr hx
    · rintro ⟨p,hp,hx⟩; obtain ⟨p,rfl⟩ := (StepData.sendBonds s (0:Site c)).surjective p
      change s.act x ∈ pinPos (sendEdge s 0 p) at hx; rw [pin_send,turn_image] at hx; exact ⟨p,(turn_aisles ..).mpr hp,hx⟩

lemma turn_dome (A : Stores S) (r : ℕ) (x : Site c) : x∈(turnStore s A).dome r ↔ s.act x∈A.dome r := by
  unfold dome; rw [halo_spec,halo_spec]; constructor
  · rintro ⟨y,hy,hh⟩; exact ⟨_,(turn_place ..).mp hy,(separation_signed ..).trans_le hh⟩
  · rintro ⟨y,hy,hh⟩; obtain ⟨z,rfl⟩ := (s.actEquiv (R:=Per c)).surjective y
    exact ⟨z,(turn_place ..).mpr hy, (separation_signed z x s).symm.trans_le hh⟩

lemma turn_flag_actual (V : Config G n) (t : ℝ) (i : Site n) :
    i ∈ RG.flags t (pull s 0 V) ↔ s.act i ∈ RG.flags t V := by
  have he := Work.H03.flags_send s (0:Site n) t V
  have ha : affine s (0:Site n)=s.act := funext fun _ => add_zero _
  rw [ha] at he
  rw [← he,turn_image]

/-- Pull the actual replica before reading any affine jets. No assertion
about charts globally, and no gauge convention on periodic seams. -/
lemma replica_turn (S : StepData c f) (V : Config G c) :
    pull s 0 (replica S.ratio V)=replica S.ratio (pull s 0 V) := by
  let g := S.ratio
  have hr (i : Site f) : g.parent (s.act i) = s.act (g.parent i) := g.parent_signed S.patch.odd_side i s
  funext e
  obtain ⟨i,j⟩ := e
  cases hx : s.flip j
  · rw [Motion.turn_read s _ _]; dsimp only; rw [edge_positive s _ hx]; unfold replica
    dsimp only; change (if s.flip j then _ else _) = if g.parent (i+step j)=g.parent i then _ else _
    rw [hx]; simp only [Bool.false_eq_true,↓reduceIte]
    rw [← step_positive s j hx i,hr,hr]
    by_cases hi : g.parent (i+step j)=g.parent i
    · simp [hi,g] at *
    have hh : s.act (g.parent (i+step j))≠s.act (g.parent i) := fun he => hi (s.act_injective he)
    rw [if_neg hh,if_neg hi,Motion.turn_read,edge_positive s _ hx]; simp [hx,g]
  · rw [Motion.turn_read s _ _]; dsimp only; rw [edge_negative s _ hx]; unfold replica
    dsimp only; change (if s.flip j then _ else _) = if g.parent (i+step j)=g.parent i then _ else _
    rw [hx]; simp only [↓reduceIte,sub_add_cancel]
    rw [← step_negative s j hx i,hr,hr]
    by_cases hi : g.parent (i+step j)=g.parent i
    · simp [hi,g] at *
    have hh : s.act (g.parent i)≠s.act (g.parent (i+step j)) := fun he => hi (s.act_injective he.symm)
    rw [if_neg hh,if_neg hi,Motion.turn_read,edge_negative s _ hx]
    have he := g.parents_hop S.patch.odd_side i j
    split at he
    · change _⁻¹=_
      have hP := step_negative s _ hx (g.parent i)
      rw [he, hP]; simp [hx,g]
    exact (hi he).elim
end turns

/-- Enough space to charge the H_D factor as one packet; always available
when O=A, including the empty case. No *construction* of connected
labels implicit. Parameter radius includes the needed buffers at uses.
Overlap (or coincident seeds) inside O okay. -/
structure Clearance (O A : Stores S) (r : ℕ) : Prop where
  fine : O.costs ⊆ A.costs
  noise : O.aisles ⊆ A.aisles
  flags : O.flags ⊆ A.flags
  freeFine (i : Cell f) : i ∈ A.costs → i∉ O.costs → Disjoint (startPos S i) (O.dome r)
  freeNoise (i : Bond c) : i ∈ A.aisles → i∉ O.aisles → Disjoint (pinPos i) (O.dome r)
  freeFlag (i : Site c) : i ∈ A.flags → i ∉ O.flags → i ∉ O.dome r



lemma expand_dome (O : Stores S) {r u : ℕ} (h : r ≤ u) : O.dome r ⊆ O.dome u :=
  Corona.halo_mono h (fun _ h => h)

lemma enter_dome (O : Stores S) {a b : Site c} {k r : ℕ} (h : a∈O.dome k) (he : k+separation a b ≤ r) :
    b∈O.dome r := by
  obtain ⟨z,hz,hz'⟩ := halo_spec.mp h
  exact halo_spec.mpr ⟨z,hz,(separation_triangle ..).trans ((Nat.add_le_add_right hz' _).trans he)⟩

namespace Clearance
variable {O A : Stores S} {r : ℕ} (h : Clearance O A r)
include h

lemma shrink {u : ℕ} (hu : u ≤ r) : Clearance O A u :=
  ⟨h.fine,h.noise,h.flags,fun i a b => (h.freeFine i a b).mono_right (expand_dome O hu),
    fun i a b => (h.freeNoise i a b).mono_right (expand_dome O hu),fun i a b hx => h.freeFlag i a b (expand_dome O hu hx)⟩

lemma turn (s : Signed) : Clearance (turnStore s O) (turnStore s A) r := by
  refine ⟨fun i hi => (turn_costs ..).mpr (h.fine ((turn_costs ..).1 hi)),
    fun i hi => (turn_aisles ..).mpr (h.noise ((turn_aisles ..).1 hi)),fun i hi => (turn_flags ..).mpr (h.flags ((turn_flags ..).1 hi)),
    fun i a b => ?_,fun i a b => ?_,fun i a b hi => ?_⟩
  · have he := h.freeFine (faces s f i) ((turn_costs ..).1 a) (mt (turn_costs s O i).2 b)
    rw [start_send s] at he
    exact Finset.disjoint_left.mpr fun x hx hy => Finset.disjoint_left.mp he ((turn_image ..).mpr hx) ((turn_dome ..).mp hy)
  · have he := h.freeNoise (sendEdge s 0 i) ((turn_aisles ..).1 a) (mt (turn_aisles s O i).2 b)
    rw [pin_send s] at he
    exact Finset.disjoint_left.mpr fun x hx hy => Finset.disjoint_left.mp he ((turn_image ..).mpr hx) ((turn_dome ..).mp hy)
  exact h.freeFlag _ ((turn_flags ..).mp a) (mt (turn_flags s O i).mpr b) ((turn_dome ..).mp hi)

lemma owns (x : ℝ) (he : 5*radiusB x ≤ r) : Owns O A x := by
  obtain ⟨ha,hb,hc,hf,hg,h'⟩ := h.shrink he
  exact ⟨ha,hb,hc,hf,hg,h'⟩

lemma home : O.place ⊆ A.place := by
  unfold place
  gcongr <;> first | exact h.fine | exact h.noise | exact h.flags

lemma all (u : ℕ) : O.dome u ⊆ A.dome u := Corona.halo_mono le_rfl h.home

lemma owns_place {i : Site c} (ha : i∈O.dome r) (hb : i∈A.place) : i∈O.place := by
  simp only [place,Finset.mem_union,Finset.mem_biUnion] at hb ⊢
  rcases hb with (⟨j,hj,hh⟩|⟨j,hj,hh⟩)|hv
  · by_cases hy : j∈O.costs
    · exact Or.inl (Or.inl ⟨j,hy,hh⟩)
    exact (Finset.disjoint_left.mp (h.freeFine j hj hy) hh ha).elim
  · by_cases hy : j∈O.aisles
    · exact Or.inl (Or.inr ⟨j,hy,hh⟩)
    exact (Finset.disjoint_left.mp (h.freeNoise j hj hy) hh ha).elim
  · exact Or.inr (Classical.not_not.mp (fun hc => h.freeFlag i hv hc ha))

lemma owns_dome {i : Site c} {d q : ℕ} (ha : i∈O.dome d) (hr : d+q ≤ r) (hb : i∈A.dome q) : i∈O.dome q := by
  obtain ⟨j,hj,hj'⟩ := halo_spec.mp hb
  refine halo_spec.mpr ⟨j,h.owns_place ?_ hj,hj'⟩
  exact enter_dome O ha ((Nat.add_le_add_left ((separation_comm ..).trans_le hj') _).trans hr)
end Clearance

end YM.AnalyticBridge.Annulus
