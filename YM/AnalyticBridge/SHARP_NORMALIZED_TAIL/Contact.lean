import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Accumulator
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Census


/-!
# Tag & sample alignment on assembled store sectors

Here: `fog` implementation. This is not trying to contract tag ports of
*another* mixed or affine covariance prescription: all on the exact one
chosen. Use tag-locality of a column of the *move* matrix on this sector
and compare window membership for the needed column inverses.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp.Contact
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Wilson Tree MeasureTheory Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open YM.Push.SectorMeasure YM.Push.SectorMeasure.Oriented Finset Inventory Almanac Presented
open Precision Exterior SectorNext.Remainder
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius YM.Push.SectorMeasure

variable {c f : Side} {G : Gauge} {x W : ℝ} {S : StepData c f} {T : Tube G S} {P : Teller G}
  {R : Rep G f} {D : Allocation G S x W} {F : Forest S.ratio} {V : Config G c} {L : Almanac T D R F}
  {A B : Stores S} {k l : S.Choices} {X : Support c}

abbrev arc (a : Rows.In x A F (G:=G)) := a.1.val.val
abbrev atSite (a : Rows.In x A F (G:=G)) := S.ratio.parent (arc a).1

-- the SAME physical bond/color
structure Pins (a : Rows.In x A F (G:=G)) (b : Rows.In x B F (G:=G)) : Prop where
  coord : a.2=b.2
  slot : a.1.val=b.1.val

private lemma unit (a : Rows.In x A F (G:=G)) : fresh x (shots S x) A F (axisPrice a) =
    Pi.single (arc a) (EuclideanSpace.basisFun G.ColorIndex ℝ a.2) := by
  rw [on_axis]
  funext i
  unfold fresh
  by_cases h : i=arc a
  · subst i; rw [Pi.single_eq_same,dif_pos a.1.val.property,dif_pos (show ¬chill _ _ _ _ from a.1.property)]
    change Pi.single _ _ a.1=_; rw [Pi.single_eq_same]
  rw [Pi.single_eq_of_ne h]; split
  · split
    · rename_i hs hm
      exact Pi.single_eq_of_ne (show (⟨⟨i,hs⟩,hm⟩ : Active A x F) ≠ a.1 from
        fun he => h (congr_arg (fun z : Active A x F => z.val.val) he)) ..
    · rfl
  · rfl

private lemma turn_pred {s : Signed} {i : Bond c} (h : S.patch.Branches S.kernel G)
    (he : Tags.Synchronized X k l) (hx : (sendEdge s 0 i).1 ∈ X)
    (hv : (sendEdge s 0 i).1+Lattice.step (sendEdge s 0 i).2 ∈ X) : blockJet V k s i=blockJet V l s i := by
  have ht (d : Directions G f) : predictGroup V k s i d=predictGroup V l s i d := by
    unfold predictGroup facade
    rw [(carry s h k _).2,(carry s h l _).2]
    have hp := Drain.pred_tags (U:=increment (replica S.ratio V) d) he (sendEdge s 0 i) hx hv
    unfold pull Step.read; unfold sendEdge at hp; split <;> rw [hp]
  unfold blockJet; simp_rw [predictorTurn,ht]

lemma with_pin (h : S.patch.Branches S.kernel G) {a : Rows.In x A F (G:=G)} {b : Rows.In x B F (G:=G)}
    (hp : Pins a b) (he : Tags.Synchronized X k l)
    (hv : halo (Next.SectorChange.span S.patch x+2) {atSite a} ⊆ X) (i) :
    Rows.move T x V k (shots S x) A F i a=Rows.move T x V l (shots S x) B F i b := by
  rcases i with ⟨⟨s,j⟩,d⟩
  have hh : arc a=arc b := congr_arg Subtype.val hp.slot
  simp only [Rows.move,of_apply,selected_all T _ _ _ _ _ _ h]; simp only [unit,tape_read, Pi.smul_apply]
  rw [← hp.coord, ← hh]
  change (slip • bump T x V k _ (s,j)) d=(slip • bump T x V l _ (s,j)) d
  let p : Directions G f := Pi.single (arc a) (EuclideanSpace.basisFun G.ColorIndex ℝ a.2)
  suffices ht : bump T x V k p (s,j) = bump T x V l p (s,j) from congr_arg (fun z : G.Color => (slip • z) d) ht
  rcases j with j|j
  · simp only [bump,Sum.elim_inl]
  by_cases hr : arc a∈shots S x s (.inr j)
  · let u := sendEdge s 0 j
    have hy : separation (atSite a) u.1 ≤ Next.SectorChange.span S.patch x+1 := by
      have ho := (contains ..).mp hr
      rw [separation_comm] at ho
      exact (separation_triangle _ (s.act j.1) _).trans (Nat.add_le_add ho (Drain.shiftedQ j s))
    have h₁ : u.1 ∈ X := hv (halo_spec.mpr ⟨atSite a,mem_singleton_self _,hy.trans (by omega)⟩)
    have h₂ : u.1+Lattice.step u.2 ∈ X := hv (halo_spec.mpr ⟨atSite a,mem_singleton_self _, (separation_triangle _ u.1 _).trans (by have hh := Work.E03.sep_step u.1 u.2; omega)⟩)
    simp only [bump,Sum.elim_inr]; unfold noiseKick; rw [turn_pred (V:=V) h he h₁ h₂]
  have hs (k : S.Choices) : bump T x V k p (s,.inr j)=0 := by
    rw [bump_dep T x V k _ _ p 0 h ?_]
    · simp [bump,noiseKick]
    intro e he; exact Pi.single_eq_of_ne (ne_of_mem_of_not_mem he hr) _
  exact (hs k).trans (hs l).symm

lemma gram_read (h : S.patch.Branches S.kernel G) {a a' : Rows.In x A F (G:=G)}
    {b b' : Rows.In x B F (G:=G)} (hp : Pins a b) (hq : Pins a' b')
    (he : Tags.Synchronized X k l)
    (hv : halo (Next.SectorChange.span S.patch x+2) {atSite a} ⊆ X)
    (hz : halo (Next.SectorChange.span S.patch x+2) {atSite a'} ⊆ X) :
    Rows.gram T x V k (shots S x) A F a a'=Rows.gram T x V l (shots S x) B F b b' := by
  unfold Rows.gram
  rw [Matrix.mul_apply,Matrix.mul_apply]; simp only [transpose_apply]
  exact sum_congr rfl fun i _ => by rw [with_pin h hp he hv i, with_pin h hq he hz i]
end YM.AnalyticBridge.Sharp.Contact
