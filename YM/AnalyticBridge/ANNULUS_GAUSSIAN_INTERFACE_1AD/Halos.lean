import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Guard
import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Turn

/-!
# Retained Wide prerequisites through the collar

One actual packet nonzero already confers Wide in each oriented channel
(including frame mass support even on fallbacks), *without checking
realizability of the rest of the Stores field*. K adjoined later.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric Oriented Presented Exterior Bloch
open YM.Next.SectorChange YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset Affine
variable {c f : Side} {G : Gauge} {S : StepData c f}

lemma exact_turn (s : Signed) (V : Config G c) (i : Site c) (t : ℝ) :
    i∈RG.flags t (pull s 0 V) ↔ s.act i∈RG.flags t V := by
  rw [← Work.H03.flags_send s (0:Site c) t V]; unfold affine; simp only [add_zero,mem_image]
  exact ⟨fun hi => ⟨i,hi,rfl⟩, fun ⟨_,hh,he⟩ => s.act_injective he ▸ hh⟩

private lemma shift {X E H Y : Finset (Site c)} (s : Signed) (h : ¬ Disjoint X E) (he : Y = E.image s.act)
    (hl : ∀ i ∈ X,s.act i∈H) : ¬Disjoint Y H := by
  intro hy; apply h; apply disjoint_left.mpr; intro i hi ht
  exact disjoint_left.mp hy (he ▸ mem_image_of_mem _ ht) (hl i hi)

lemma force_wide {q : Chi} {A O : Stores S} {x w : ℝ} {D : ℕ} {N : Support c}
    {U : Config G f} {V : Config G c} {k : S.Choices}
    (hh : S.patch.Branches S.kernel G) (hw : 0<w) (hT : 0 < fiery G x S.patch.L) (hN : O.dome ((D+5)*radiusB x) ⊆ N)
    (h : receipts q A x w N (nearFace S N) (nearNoise N) U V k ≠ 0) (s : Signed) :
    Wide (turnStore s O) (turnStore s A) D x w (pull s 0 U) (choice s k) (pull s 0 V) := by
  let X := (turnStore s O).dome ((D+5)*radiusB x)
  have he (i) (hi : i∈X) : s.act i∈N := hN ((dome_turn ..).1 hi)
  unfold receipts profilesHere prayersHere at h
  have hf := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have ht := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hm := left_ne_zero_of_mul (right_ne_zero_of_mul h)
  constructor
  · intro p hp
    have hb : Face.send s 0 p ∈ nearFace S N :=
      mem_filter.mpr ⟨mem_univ _,shift s hp (startPos_turn s p) he⟩
    have hu := profile_charged q A.costs (toll U) (by linarith : 0 < fiery G x S.patch.L/4) _
      (prod_ne _ (left_ne_zero_of_mul hf) hb) (G.chord_nonneg _)
    rw [costs_turn]
    rw [show toll (pull s 0 U) p=toll U (Face.send s 0 p) from Face.send_price U p s 0 G.chord G.chord_inv fun k g => G.chord_conj g k]
    refine ⟨fun hl => (hu.1 hl).le,fun hl => (hu.2 hl).le.trans_eq ?_⟩; ring
  · intro i hi
    have hb : sendEdge s 0 i∈nearNoise N := mem_filter.mpr ⟨mem_univ _,shift s hi (pinPos_turn s i) he⟩
    have hr (j : Bond c) : 0 ≤ wire (S.prediction U k) V j := G.chord_nonneg _
    have hu := profile_charged q A.aisles (wire (S.prediction U k) V) (mul_pos hw hT) _
      (prod_ne _ (right_ne_zero_of_mul hf) hb) (hr _)
    rw [aisle_turn,(Oriented.carry s hh k U).2,wire_pulled]
    exact ⟨fun hl => (hu.1 hl).le,fun hl => by rw [mul_assoc]; exact (hu.2 hl).le⟩
  · intro i hi
    rw [flag_turn,exact_turn]
    have hx := prod_ne _ ht (he i hi)
    unfold flag at hx; split at hx
    next hv => exact hv
    contradiction
  intro i hi; rw [frame_turn hh]
  exact lt_of_le_of_ne' (frame_zero k U _) (prod_ne _ hm (he i hi))



/-- In particular every actual fine flag at packet q-eligible or
q-suppressed query sites (include the projection at the same physical halo) is
touched by a *physical nondefault* fine plaquette. Thus can demand K
incidence here too; stronger intact-sector version for any flag unconditionally
given by Allocation.flagged. -/
lemma local_flagged {A : Stores S} {N : Support c} {q : Chi} {x w : ℝ} {U : Config G f} {V : Config G c}
    {k : S.Choices} (h : receipts q A x w N (nearFace S N) (nearNoise N) U V k ≠ 0)
    (he : 0<fiery G x S.patch.L) (i : Site f) (hi : S.ratio.parent i∈N) (hv : i∈RG.flags (fiery G x S.patch.L) U) :
    ∃ p∈A.costs, i ∈ touched p := by
  obtain ⟨p,hp,hp'⟩ := (flags_spec ..).mp hv
  refine ⟨p,?_,hp⟩
  have hx : p ∈ nearFace S N := by
    apply mem_filter.mpr
    exact ⟨mem_univ _,fun h => disjoint_left.mp h (Finset.mem_image_of_mem _ hp) hi⟩
  have ht := prod_ne _ (left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul h))) hx
  have hu := (profile_charged q A.costs (toll U) (by linarith : 0<fiery G x S.patch.L/4) p ht (G.chord_nonneg _)).2
  by_contra hg
  have hv := hu hg
  change _ < toll U p at hp'; linarith

end YM.AnalyticBridge.Annulus1AD
