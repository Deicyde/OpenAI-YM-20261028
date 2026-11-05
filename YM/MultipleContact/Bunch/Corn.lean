import YM.Further.LOCAL_LOG_JETS.Series
import YM.MergeProof.Buys
import YM.MergeProof.North.Fermi
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Kin
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi

/- generalized from YM.MergeProof.North.Corn to arbitrary arity -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory 
open Push Marker Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Trajectories
open scoped Topology BigOperators Classical
variable {V ι J : Type}[Fintype V][DecidableEq V]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Aged V slot
variable (c₀:V) (b:Equiv.Perm V)(m: Motion)
def Harm (x y: Poly (Aged V slot)):=∀ p, Focused c₀ p→ y.part (drum (slot:=slot) b p)=scalar m (x.part p)
lemma scales (i:Finset J)(x:J→ℂ): ∑ j∈i,scalar m (x j)=scalar m (∑ j∈i,x j):=by unfold scalar;split<;> first|rw [star_sum]|rfl
variable {c₀ b m}
lemma monoFocus {p q:(X).Mode}(h:p.val⊆q.val)(he:Focused c₀ q): Focused c₀ p:= (Finset.image_subset_image h).trans he
namespace Harm
variable {x y z w:Poly (Aged V slot)}(H:Harm c₀ b m x y)
include H
lemma mul (h:Harm c₀ b m z w): Harm c₀ b m (x*z) (y*w):=by
    intro p hp; rw [Poly.part_mul, Poly.part_mul, ← Equiv.sum_comp (drum (slot:=slot) b),← scales]; refine sum_congr rfl fun i _=>?_
    rw [← Equiv.sum_comp (drum (slot:=slot) b),← scales]; refine sum_congr rfl fun j _=>?_
    have hs: Poly.merges i j p↔ Poly.merges (drum (slot:=slot) b i) (drum (slot:=slot) b j) (drum (slot:=slot) b p):=by
       unfold Poly.merges; simp only [drum,pares,← Finset.image_union]; exact and_congr ((Finset.disjoint_image (nome (slot:=slot) b).injective).symm) (Finset.image_injective (nome (slot:=slot) b).injective|>.eq_iff.symm)
    by_cases hh:Poly.merges i j p
    · rw [if_pos hh,if_pos (hs.mp hh),H i (monoFocus (hh.2 ▸ Finset.subset_union_left) hp),h j (monoFocus (hh.2 ▸ Finset.subset_union_right) hp),scalar_mul]
    rw [if_neg hh,if_neg (fun e=> hh (hs.mpr e)),scalar_z]

omit H
lemma agone : Harm (slot:=slot) c₀ b m 1 1:=fun p hp=> by
   have he : drum (slot:=slot) b p=(X).quiet ↔ p=(X).quiet:=by nth_rw 1 [← show drum (slot:=slot) b (X).quiet=(X).quiet from Subtype.ext (by simp [drum,pares,Census.quiet])]; exact (drum (slot:=slot) b).apply_eq_iff_eq
   simp [Poly.one_part,he,Motion.scalar]
lemma seq (s:Finset ι)(x y:ι→ Poly (Aged V slot))(h:∀ i∈s,Harm c₀ b m (x i) (y i)): Harm c₀ b m (∑ i∈s,x i) (∑ i∈s,y i):=by
   intro p hp; simp only [Poly.part_sum, ← scales]; exact sum_congr rfl fun i hi=> h i hi p hp
lemma prod_ (s:Finset ι)(x y:ι→ Poly (Aged V slot))(h:∀ i∈s,Harm c₀ b m (x i) (y i)): Harm c₀ b m (∏ i∈s,x i) (∏ i∈s,y i):=by
   induction s using Finset.induction with
   | empty=> simp only [Finset.prod_empty]; exact agone
   | insert i s hi ih=> rw [prod_insert hi,prod_insert hi]; exact (h _ (mem_insert_self ..)).mul (ih (fun _ hh=> h _ (mem_insert_of_mem hh)))
lemma solo (p:(X).Mode)(f:ℂ) : Harm c₀ b m (Poly.send p f) (Poly.send (drum (slot:=slot) b p) (Motion.scalar m f)):=by
   intro i hi; simp only [Poly.part_send,Equiv.apply_eq_iff_eq];split; rfl; exact (scalar_z _).symm
end Harm
end YM.MergeProof.BatchRibbons
