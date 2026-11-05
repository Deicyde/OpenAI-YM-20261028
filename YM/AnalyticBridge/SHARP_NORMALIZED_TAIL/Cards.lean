import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Requests
import YM.Push.SECTOR_MEASURE.Cells
import YM.Work.B04
import YM.Work.B06
import YM.Work.E01


/-!
# Inventory used by the estimate

In particular, exact all physical output flags coverage (a sector with
wrong inventory doesn't get to omit a negative test). The label inventory
includes all patch locations at which seeds are sold. This is a
point-estimate submodule; not claiming these sets certify locality of any
resulting activities wrt V. Use full supports when combining with such
budgets.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Filter Function Lattice RG Pressure Pressure.Stores Wilson Finset SectorNext.Vacuum.ReLog
open YM.Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure

variable {c f : Side} {ι E : Type} [DecidableEq E]
  {S : StepData c f}

namespace Inventory

/-- Physical expenditure currencies; disjoint even at the same location. -/
abbrev Seed (c f : Side) := (Cell f ⊕ Bond c) ⊕ Site c
abbrev Token (_S : StepData c f) (E : Type) := Seed c f ⊕ E

def items (A : Stores S) : Finset (Seed c f) :=
  (A.costs.disjSum A.aisles).disjSum A.flags

def request (A : Stores S) (H : Finset E) : Finset (Token S E) := (items A).disjSum H

def anchor (S : StepData c f) : Seed c f → Site c := Sum.elim
  (Sum.elim (fun i => S.ratio.parent i.1) Prod.fst) id

lemma card_items (A : Stores S) : (items A).card = A.shares := by simp [items,shares]

lemma attached (A : Stores S) (i) (h : i∈items A) : anchor S i ∈ A.place := by
  rcases i with (p|b)|x
  · simp only [items, inl_mem_disjSum] at h
    refine mem_union_left _ (mem_union_left _ (mem_biUnion.mpr ⟨p,h,
      mem_image_of_mem _ (Work.E01.base_touched p)⟩))
  · simp only [items, inl_mem_disjSum,inr_mem_disjSum] at h
    exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨b,h,by simp [pinPos,anchor]⟩))
  simp only [items,inr_mem_disjSum] at h
  exact mem_union_right _ h




/-- Ask S,N at least here and D' *exactly*. -/
def zone (D : Stores S) : Finset (Stores S) := univ.filter fun A =>
    D.costs ⊆ A.costs ∧ D.aisles ⊆ A.aisles ∧ A.flags=D.flags





/-- Whole fixed price per claimed seed. -/
def bill (S : StepData c f) (R : ℝ) (w : E → ℝ) : Token S E → ℝ := Sum.elim (fun _ => Real.exp R) w
lemma charges (R : ℝ) (w : E → ℝ) (D : Stores S) (n : Finset E) :
    (∏ i∈request D n,bill S R w i)=Real.exp (R*D.shares)* ∏ t∈n,w t := by
  rw [mul_comm R _, Real.exp_nat_mul]; simp [bill, request, prod_disjSum,card_items]

end Inventory
open Inventory

/-- Seed/overlap annotations of local terms. Using only these annotations
and pairwise site overlaps for the gas *requires* the accompanying literal
sector expansion. Not assuming it holds when labels first arrive. -/
structure Cards (S : StepData c f) (ι E : Type) where
  seeds : ι → Stores S
  marks : ι → Finset E
  X : ι → Support c
  posts : E → Site c
  full i : (X i).Nonempty
  gate i : (seeds i).place ⊆ X i
  around i e : e∈marks i → posts e ∈ X i

namespace Cards
variable (K : Cards S ι E)

def claims : Claims (Site c) ι (Token S E) where
  supp := K.X
  full := K.full
  tokens i := request (K.seeds i) (K.marks i)
  loc := Sum.elim (anchor S) K.posts
  binds i e he := by
    rcases e with k|t
    · exact K.gate i (attached _ k (inl_mem_disjSum.mp he))
    exact K.around i t (inr_mem_disjSum.mp he)

def ports (P : Finset ι) : Stores S :=
  ⟨P.biUnion fun i => (K.seeds i).costs,P.biUnion fun i => (K.seeds i).aisles,
    P.biUnion fun i => (K.seeds i).flags⟩




variable (u : ι → ℝ) (A : Stores S) (m : Finset E)

/-- Which terms are emitted from the expansion of the indicated sector.
We aggregate nothing on coincident geometric supports. -/
def Makes (Q : Finset ι) := (Q:Set ι).PairwiseDisjoint K.X ∧ K.ports Q=A ∧ Q.biUnion K.marks=m

def check (Q : Finset ι) := if K.Makes A m Q then ∏ i∈Q,u i else 0






end Cards
end YM.AnalyticBridge.Sharp
