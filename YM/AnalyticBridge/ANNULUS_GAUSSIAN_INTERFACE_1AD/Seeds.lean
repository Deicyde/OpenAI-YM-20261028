import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE_1AD.Turn

/-!
# Separated typed seed packets, E: gas 7001

R parameter in B units (500 in E). Different responsibilities even
at coincident sites. Don't require maximal connectivity in the payment
statement; permit also merged packets, and still on a genuine torus.
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

variable {c f n : Side} {S : StepData c f}

open Finset

/-- Sigma type in one channel/orientation only. Sum type keeps even
coincident addresses from different kinds. -/
abbrev Mark (_ : StepData c f) := (Cell f ⊕ Bond c) ⊕ Site c

def planted (A : Stores S) (m : Mark S) : Prop :=
  m.elim (Sum.elim (·∈A.costs) (·∈A.aisles)) (·∈A.flags)

def plots (A : Stores S) : Finset (Mark S) := univ.filter (planted A)

def spotting (S : StepData c f) (m : Mark S) : Support c :=
  m.elim (Sum.elim (startPos S) pinPos) fun i => {i}

lemma planted_owns (A : Stores S) (i : Site c) :
    i∈A.place ↔ ∃ p : Mark S, planted A p ∧ i∈spotting S p := by
  simp only [place,mem_union,mem_biUnion]
  constructor
  · rintro ((⟨p,hp,hi⟩|⟨b,hb,hi⟩)|h)
    · exact ⟨.inl (.inl p),hp,hi⟩
    · exact ⟨.inl (.inr b),hb,hi⟩
    exact ⟨.inr i,h,mem_singleton_self _⟩
  rintro ⟨(p|b)|q,hp,hi⟩
  · exact Or.inl (Or.inl ⟨p,hp,hi⟩)
  · exact Or.inl (Or.inr ⟨b,hp,hi⟩)
  exact Or.inr (mem_singleton.mp hi ▸ hp)

lemma place_plots (A : Stores S) : A.place = (plots A).biUnion (spotting S) := by
  ext i; simp [planted_owns,plots]




-- cardinality counts types, not hull positions (e.g. seams don't change this bill)


lemma plots_sub (O A : Stores S) : plots O ⊆ plots A ↔
    O.costs ⊆ A.costs ∧ O.aisles ⊆ A.aisles ∧ O.flags ⊆ A.flags := by
  simp only [Finset.subset_iff,plots,mem_filter,mem_univ,true_and]
  constructor
  · intro h
    exact ⟨fun p => @h (Sum.inl (.inl p)),fun i => @h (Sum.inl (.inr i)),fun i => @h (Sum.inr i)⟩
  rintro ⟨h,h',k⟩ ((i|i)|i) <;> first | exact @h i | exact @h' i | exact @k i

/-- Compulsory packets OR their unions. Use R = 500B for the ordinary
single packet, introduced in raw graph units here. -/
structure Packet (O A : Stores S) (R : ℕ) : Prop where
  subset_plots : plots O ⊆ plots A
  alone : ∀ i : Mark S, planted A i → ¬planted O i → Disjoint (halo R (spotting S i)) (O.dome R)

namespace Packet
variable {O A : Stores S} {R M : ℕ}


lemma recognizes (h : Packet O A R) :
    O.costs ⊆ A.costs ∧ O.aisles ⊆ A.aisles ∧ O.flags ⊆ A.flags := (plots_sub O A).mp h.subset_plots
lemma carry (h : Packet O A R) (hm : M ≤ R) : Packet O A M := ⟨h.subset_plots, fun i hi ht =>
  Disjoint.mono (Corona.halo_mono hm (Subset.refl _)) (Corona.halo_mono hm (Subset.refl _)) (h.alone i hi ht)⟩
lemma place_near (h : Packet O A R) {p : Site c} (hp : p∈A.place) (hf : p∈O.dome R) : p∈O.place := by
  obtain ⟨m,ha,hb⟩ := (planted_owns ..).mp hp
  by_contra he
  exact disjoint_left.mp (h.alone m ha (fun ht => he ((planted_owns _ _).mpr ⟨m,ht,hb⟩))) (halo_subset R _ hb) hf
lemma zone_transfer (h : Packet O A R) {X x : ℕ} {p : Site c} (hM : X+x ≤ R)
    (hp : p∈O.dome X) (ha : p∈A.dome x) : p∈O.dome x := by
  obtain ⟨l,hl,ht⟩ := halo_spec.mp ha
  obtain ⟨q,hq,hd⟩ := halo_spec.mp hp
  have hT : l∈O.dome R := halo_spec.mpr ⟨q,hq,(separation_triangle q p l).trans (by rw [separation_comm p l]; omega)⟩
  exact halo_spec.mpr ⟨l,h.place_near hl hT,ht⟩

lemma halo_turn {b : ℕ} {s : Signed} {D E : Finset (Site c)} (h : E = D.image s.act) {i : Site c} :
    i∈halo b D → s.act i ∈ halo b E := by
  intro hi; obtain ⟨l,hl,hL⟩ := halo_spec.mp hi
  exact halo_spec.mpr ⟨s.act l,h ▸ mem_image_of_mem _ hl,by rwa [separation_signed]⟩

lemma turns (h : Packet O A R) (s : Signed) : Packet (turnStore s O) (turnStore s A) R := by
  obtain ⟨hl,hp,hα⟩ := h.recognizes
  constructor
  · exact (plots_sub _ _).mpr ⟨fun i hi => (costs_turn ..).mpr (hl ((costs_turn ..).mp hi)),
        fun i hi => (aisle_turn ..).mpr (hp ((aisle_turn ..).mp hi)),
        fun i hi => (flag_turn ..).mpr (hα ((flag_turn ..).mp hi))⟩
  intro m hm hq
  apply disjoint_left.mpr; intro i hv hi
  have hi := (dome_turn ..).mp hi
  obtain (p|b)|l := m
  · exact disjoint_left.mp
      (h.alone (.inl (.inl (Face.send s 0 p))) ((costs_turn s A p).mp hm) (fun ht => hq ((costs_turn ..).mpr ht)))
      (halo_turn (startPos_turn s p) hv) hi
  · exact disjoint_left.mp (h.alone (.inl (.inr (sendEdge s 0 b))) ((aisle_turn s A b).mp hm)
      (fun ht => hq ((aisle_turn ..).mpr ht))) (halo_turn (pinPos_turn s b) hv) hi
  exact disjoint_left.mp (h.alone (.inr (s.act l)) ((flag_turn s A l).mp hm) (fun ht => hq ((flag_turn ..).mpr ht)))
    (halo_turn (Finset.image_singleton (Signed.act s) l).symm hv) hi

lemma ownership {x : ℝ} (h : Packet O A R) (hx : 5*radiusB x ≤ R) : Affine.Owns O A x := by
  obtain ⟨hf,hb,hj⟩ := h.recognizes
  have hh := h.carry hx
  refine ⟨hf,hb,hj,fun p hp he => ?_,fun p hp he => ?_,fun p hp he hv => ?_⟩
  · exact Disjoint.mono_left (halo_subset _ _) (hh.alone (.inl (.inl p)) hp he)
  · exact Disjoint.mono_left (halo_subset _ _) (hh.alone (.inl (.inr p)) hp he)
  exact disjoint_left.mp (hh.alone (.inr p) hp he) (halo_subset _ _ (mem_singleton_self p)) hv



end Packet
end YM.AnalyticBridge.Annulus1AD
