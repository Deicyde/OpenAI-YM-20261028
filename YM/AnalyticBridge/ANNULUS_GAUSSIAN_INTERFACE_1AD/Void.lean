import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Push.SECTOR_MEASURE.Profile
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Delay


/-!
# The incoming compulsory flag decisions, on the same U

Not paid or relocated as K activities. Keep the address set, q membership
against ORIGINAL supports (not the inspected one), and pass the incidence
condition to any other recipe even if dropping background defaults later.
Part of  even for regions with no off-flag stability.
-/
set_option autoImplicit false
-- Only stylistic lint disabled. All holes/axioms/declaration safety audited at entry.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.AnalyticBridge.Annulus1AD
open Filter Function Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube MeasureTheory Tree
   Axial YM.Push.SectorMeasure Next.Fluctuations Metric   Exterior Bloch
open  YM.SectorNext.Remainder
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff
open Finset
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Output support for deciding q usage still includes *every* i queried,
even when q=1 because already covered by a K address. Not a support
certificate (see e.g.  for one-time read halo needed in integration). -/
def covered (N : Support c) (S : StepData c f) : Finset (Site f) := univ.filter fun i => S.ratio.parent i∈N


def vflag (A : Activities G f) (P : BudgetPoint) (U : Config G f) (b : Finset ℕ) (i : Site f) : ℝ :=
  if i∈b.biUnion (fun j => (A.forced j).support) ∨ i∉RG.flags P.threshold U then 1 else 0

lemma vflag_price (A : Activities G f) (P : BudgetPoint) (U : Config G f) (b : Finset ℕ) (i : Site f) :
    vflag A P U b i∈Set.Icc (0:ℝ) 1 := by unfold vflag; split <;> norm_num

def voids (A : Activities G f) (P : BudgetPoint) (U : Config G f) (b : Finset ℕ) (s : Finset (Site f)) : ℝ :=
  ∏ i∈s,vflag A P U b i



lemma violation {A : Activities G f} {P : BudgetPoint} {U : Config G f} {b : Finset ℕ} {s : Finset (Site f)}
    (h : voids A P U b s ≠ 0) {i : Site f} (he : i∈s) (ht : i∉b.biUnion (fun j => (A.forced j).support)) :
    i∉RG.flags P.threshold U := by
  intro hw; apply h
  unfold voids; apply prod_eq_zero he
  simp [vflag,ht,hw]



/-- Static incidence must be retained in later recipes. In particular,
if a K occurrence is assigned at one of its flag sites, its projected
support intersects the compulsory packet containing the witnessing seed.
-/
def insisting (P : Activities G f) (A : Stores S) (b : Finset ℕ) :=
    ∀ i ∈ b,∀ j ∈ (P.forced i).inventory, ∃ p∈A.costs, j∈touched p

lemma written_cost {x w : ℝ} (D : Allocation G S x w) {k : S.Choices} {A : Stores S}
    {U : Config G f} {V : Config G c} (h : D.bill A k U V ≠ 0)
    {P : Activities G f} {B : BudgetPoint} (hB : B.threshold=fiery G x S.patch.L)
    {b : Finset ℕ} (he : P.gasOccurrence B b U ≠ 0) : insisting P A b := by
  have hh : P.admissible B U b := fun_not_eq he
  intro i hi j hj
  apply D.flagged h j
  rw [← hB, ← hh.2]; exact mem_biUnion.mpr ⟨i,hi,hj⟩
where
  fun_not_eq (hx : P.gasOccurrence B b U ≠ 0) : P.admissible B U b := by
    by_contra he; exact hx (if_neg he)







end YM.AnalyticBridge.Annulus1AD
