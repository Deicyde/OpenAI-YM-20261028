import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pictures
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Tableau

/-!
# Leading projections of the first logarithm's inputs

Pure symbols. Test book-comp support before applying any mean replacement.
Projection zeroes unauthorized footprints on cast out marker modes. Allows
exterior flags (otherwise could talk only when ALL unmarked).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph
     Flux Bid Precision Filter Station
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {x τ : ℝ} {L : Lantern G S} {P : Teller G} {W ι α : Type} [Fintype W] [DecidableEq W]
    {u : W→ Site c}

section
variable (H : ι→ Flake S G x L.park u τ) (z : Finset W)
local notation "Q" => flakeTone ∘ H
lemma shelved (v : modes W) (c : ℂ) : bed z (Poly.send v c)= if v.val⊆z then Poly.send v c else 0:= by
  ext i; rw [Flux.shelve]; split_ifs with h ht ht <;> try rfl
  all_goals rw [Poly.part_send,if_neg] <;> first|rfl| (rintro rfl; contradiction)
lemma lacked (s : Finset ι) : cardGoal Q s=∅ ∧ glow Q s=⊥ ∧ premise Q s := ⟨by ext; simp [cardGoal,flakeTone],by simp [glow, flakeTone],
   ⟨fun _ _ _ _ _=> Finset.disjoint_empty_left _,fun _ _ _ _ _=> Finset.disjoint_empty_left _,by simp [flakeTone]⟩⟩
lemma chiseling (s : Club Q) : ¬(cardGoal Q s.val).Nonempty ∧ (fires Q s.val).val.Nonempty:= by
  constructor; rw [(lacked H _).1]; exact not_nonempty_empty
  obtain ⟨i,hi⟩:=s.property.1.1; exact (H i).nontrivial.mono (fun p ht=> mem_biUnion.mpr ⟨i,hi,ht⟩)

def tucked (s : Finset ι) : Shader G S x L.park (veil W):= fun A k U y=>bed z (risen Q s A k U y)
-- doesn't test earnings on omitted sectors
variable (ht : Boosted T P x) (U : Config G c)
def Ticketed (H : ι→ Flake S G x L.park u τ) (z : Finset W) (T : Tube G S) (U : Config G c) :=
    let Q' := flakeTone ∘ H
    ∀ s:Club Q',(fires Q' s.val).val⊆ z → validArea Q' s U ∧ ∀ k : Streak L.park,Integrable (stage Q' s.val (nohole S x U) k U) (viewer T (nohole S x U) x k.wood k.tag U)
include ht in
lemma arrivals (hU : Ticketed H z T U) (s : Finset (Club Q)) (H' : (s:Set _).PairwiseDisjoint (zone Q)) :
    let q:= draw Q s
    let X:= bed z (∏ i∈s,proceeds Q T i U)
    let A:=nohole S x U
    (∀ k,Integrable (tucked H z q A k U) (viewer T A x k.wood k.tag U))∧ glance T (tucked H z q) ⊥ U=X:= by
  intro q X A
  have hh : enlist Q q:= drew Q s H'
  have he (i) (hi:i∈s): (fires Q i.val).val ⊆ (fires Q q).val:= by intro j hj; obtain ⟨p,hp,h⟩:=mem_biUnion.mp hj; exact mem_biUnion.mpr ⟨p,mem_biUnion.mpr ⟨i,hi,hp⟩,h⟩
  by_cases h: (fires Q q).val⊆ z
  · have hz i (hi:i∈s) := hU i ((he i hi).trans h)
    have hX : X=∏ i∈s, proceeds Q T i U:= by
      unfold X; rw [map_prod]; apply prod_congr rfl; intro i hi; rw [proceeds,if_pos (hz i hi).1]; exact (shelved ..).trans (if_pos ((he i hi).trans h))
    have hu := inspected Q ht q hh U s H' rfl (fun i hi=> (hz i hi).1) (fun i hi=>by rw [(lacked H _).2.1]; exact (hz i hi).2)
    rw [hX,show tucked H z q=risen Q q from ?_]; rw [(lacked H _).2.1] at hu; exact hu
    funext A k V y; unfold tucked; rw [rising Q q hh V k y,shelved,if_pos h]
  have hv : tucked H z q=(fun _ _ _ _=> 0):= by funext A k V y; unfold tucked; rw [rising Q q hh V k y,shelved,if_neg h]
  have hX:X=0:= by
    unfold X
    by_cases hh' :∀ i∈s,validArea Q i U
    · rw [prod_congr rfl (f:=fun i=> proceeds Q T i U) (g:=fun i=> Poly.send (fires Q i.val) (letter Q (T:=T) i U)) (fun i hi=>if_pos (hh' _ hi)),party_marks Q _ H',shelved,if_neg h]
    obtain ⟨j,hj,hj'⟩:= not_forall.mp hh'|>.imp fun _=>Classical.not_imp.mp
    rw [prod_eq_zero hj (if_neg (show ¬validArea Q j U from hj')), map_zero]
  rw [hv,hX]; exact ⟨fun _=>integrable_zero .., by simp [glance]⟩
variable [Fintype ι]

def pages : Shader G S x L.park (veil W):= fun A k U y=> bed z (∏ i,(ingrain Q i A k U y + 1))
include ht
lemma impression (hU : Ticketed H z T U) : (∀ k,Integrable (pages H z (nohole S x U) k U) (viewer T (nohole S x U) x k.wood k.tag U)) ∧
    glance T (pages H z) ⊥ U=bed z (Flux.chair (zone Q) (fun i=>proceeds Q T i U) univ):= by
  let I:= univ.filter (enlist Q)
  have h : pages H z=fun A k U y=>∑ i∈I,tucked H z i A k U y:= by
    funext A k V y
    unfold pages; rw [Fintype.prod_add (fun i => ingrain Q i A k V y) (fun _=>1)]
    simp_rw [prod_const_one,mul_one,map_sum]
    symm; refine sum_subset (Finset.subset_univ I) (fun i _ hi=>?_)
    change bed z (risen Q i A k V y)=0
    rw [no_clash Q i (fun hh=>hi (mem_filter.mpr ⟨mem_univ _,(lacked H _).2.2,hh⟩)),map_zero]
  have hv k i (hi:i∈I):Integrable (tucked H z i (nohole S x U) k U) (viewer T (nohole S x U) x k.wood k.tag U):= by
    obtain ⟨s,hs,hi'⟩:= luminous Q i (mem_filter.mp hi).2
    rw [← hi']; exact (arrivals H z ht U hU s hs).1 k
  rw [h]; refine ⟨fun k=> integrable_finsetSum _ (hv k),?_⟩
  let s i := glance T (tucked H z i) (⊥ : vouchers S) U
  calc
    _ = ∑ i∈I,s i := by
      unfold s glance; dsimp only; rw [show stapled x (⊥:vouchers S) U=nohole S x U from rfl]; simp_rw [fun k=>integral_finsetSum I (hv k), smul_sum]; rw [sum_comm]
    _ = _ := by
      unfold Flux.chair; rw [powerset_univ,← Finset.sum_filter,map_sum]; symm
      apply Finset.sum_bij (fun i _=>draw Q i) (fun i hi=> ?_) (fun i hi j hj h=> ?_) (fun i hi=> ?_) (fun i hi=> ?_)
      · exact mem_filter.mpr ⟨mem_univ _,drew Q _ (mem_filter.mp hi).2⟩
      · have hz:= Eq.trans (recovered Q (mem_filter.mp hi).2).symm (by rw [h,recovered Q (mem_filter.mp hj).2]); exact Finset.image_injective Subtype.val_injective hz
      · obtain ⟨s,hs,h⟩:= luminous Q i (mem_filter.mp hi).2; exact ⟨s,mem_filter.mpr ⟨mem_univ _,hs⟩,h⟩
      exact (arrivals H z ht U hU i (mem_filter.mp hi).2).2.symm
end
end YM.PhysicalNext.InteractingRank.Display
