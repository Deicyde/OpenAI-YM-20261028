import YM.Next.RANK.Flux.Chronicle

/-!
# Use of the unmarked log and inputs

Physical test gloss:
 - Prior RG_STEP supports on every residue including winding, prove `Intervals` at
   the chosen rest. This does not ask that estimate of all admissible P and etc., or
   assert any logs for marker-extended hard-core under conditional boundaries. Use
   an unmarked-only pressure representation.
   `Intervals` involves all fields & *all holes*. Expose even for forced labels.
 - Charge weights of the first-system receipts before logs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Flux
open Marker Glyph Exponential Finset Lattice Ac Relation Value Corona RG Wilson MeasureTheory Tapes Spindle Atlas Station Peak Cells Perch Edition Filter
open scoped BigOperators Classical Topology

variable {V ι κ : Type} {G : Gauge} [DecidableEq V] [Fintype V] {n : Side} {Q : Rep G n} {ζ : V→Site n}

-- unmarked subdivision.gas formula; exact finite due grouping. Interpret partwise if using complex under chart.
variable [Fintype ι] [Fintype κ]

def backgroundU (X : ι → Inner G ζ) (t : ℝ) (R : Support n) (u : Config G n) := chair (fun i => (X i).extent)
    (fun i=>((X i).glow t).covets u) (univ.filter fun i=> Disjoint (X i).extent R)

-- Here x *before* P-coast exponent. A no marks.
variable (p : Vac ζ Q) (A : Config G n→ ℂ) (Z : ι→ Inner G ζ)

def deemed (U : Config G n) := ∏ i, ((p.pay i).covets U +1)

def reclaimed (U : Config G n) (D : Support n) := ∏ i∈ univ.filter (fun i=> ¬ Disjoint (p.holes i).extent D), (((p.holes i).glow Q.p.threshold).covets U+1)

structure Intervals : Prop where
  ears i : (Z i).fires=quiet V
  openVac D U : A U • backgroundU Z Q.p.threshold D U =((Real.exp (Q.exponent U):ℂ) • deemed p U) * reclaimed p U D

variable (X : κ → Plug G ζ Q.p.threshold)
def bouys (U : Config G n) := A U •
    ∑ t∈ univ.filter (fun t=> unmark X t (flags Q.p.threshold U)),(∏ i∈t,(X i).tolls U)* backgroundU Z Q.p.threshold (t.biUnion fun i=> (X i).extent) U

omit [Fintype κ] in
lemma overlooks (U : Config G n) (D : Finset κ) : reclaimed p U (D.biUnion (fun i=> (X i).extent)) =
    ∏ i∈ univ.filter (fun i=> earns X (measureH p) i D), ((raised (measureH p i)).covets U+1):= by
  apply Finset.prod_congr _ fun i _=>rfl; ext i; simp only [mem_filter,mem_univ,true_and];constructor
  · intro h; obtain ⟨j,hj,hg⟩:=Finset.not_disjoint_iff.mp h; obtain ⟨u,hu,hp⟩:=mem_biUnion.mp hg; exact ⟨u,hu,⟨j,hp,hj⟩,fun h=> False.elim h⟩
  rintro ⟨u,hu,⟨j,hJ,hx⟩,-⟩; exact not_disjoint_iff.mpr ⟨_,hx, mem_biUnion.mpr ⟨_,hu,hJ⟩⟩
lemma in_bulk (O : Intervals p A Z) (h : Nonempty (Embedded p.f X)) : Matric p X (bouys A Z X):= by
  refine ⟨h,fun U=> ?_⟩; let t:=deemed p U;let a:= A U; let v:ℂ:=Real.exp (Q.exponent U)
  rw [bouys,infrared,embellished,Finset.sum_mul,Finset.smul_sum,Finset.smul_sum]; apply sum_congr rfl; intro i _
  rw [← mul_smul_comm, O.openVac,overlooks];
  simp only [Algebra.smul_def,deemed]; ring
end YM.Next.Rank.Flux
