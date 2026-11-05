import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Region
import YM.Push.ABSOLUTE_SUMS.Packet
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Wisps

/-!
# Simultaneous compulsory procurements: geometry on these physical rows

Not a grammar for reconnection. This will split real masks/actual
integrands and the compulsory expenses for joint use on these arguments;
still have budgets for remaining exponent terms/dependence queries and
all reconnection choices (and no claim of independence of the Gaussian
laws or actual coarse representation). Allow splitting off even some
of the compulsory packets only (mandatory in the integrand already).
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented
open SectorNext.Remainder.Affine Harvest  Push.AbsoluteSums.Packets
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- All mandatory packets  for this A. In Stores format for the
single-packet usages. -/
def accounts (A : Stores S) (l B : ℕ) := (pieces S l B A).map (sectorAlphabet S).symm.toEmbedding

/-- Enough for a portfolio of procurements at *intact* sector
integrands, may be able to prove from other ownership rules as well.
-/
structure Itemized (A : Stores S) (l B : ℕ) (X : Finset (Stores S)) : Prop where
  owned i : i∈X → Isle i A l B
  separate : (X : Set (Stores S)).PairwiseDisjoint fun O => O.dome (l*B)

variable {l B : ℕ} {A O : Stores S}




lemma account_total {g : Stores S → ℝ} (h : ∀ p∈accounts A l B,g p = p.shares) :
    ∑ i∈accounts A l B, g i = A.shares := by
  rw [Finset.sum_congr rfl h,accounts,Finset.sum_map]
  change ∑ i∈pieces S l B A, (((store S i).shares:ℕ):ℝ) = _
  simp_rw [store_price]; norm_cast
  exact (pieces_price S l B A).2.2.2







section stacked
variable {X : Finset (Stores S)} {A : Stores S} {l : ℕ} {x : ℝ}
  (h : Itemized A l (radiusB x) X)
include h


omit h in
private lemma displaces {I K Z : Type*} (X : Finset I) (f : I → Finset K) (g : I→Finset Z) (t : Z → K)
    (h1 : ∀ i ∈ X,∀ j∈g i,t j∈f i) (h2 : (X:Set I).PairwiseDisjoint f) :
    (X : Set I).PairwiseDisjoint g := fun i hI j hJ he => Finset.disjoint_left.mpr fun k hki hkj =>
  Finset.disjoint_left.mp (h2 hI hJ he) (h1 i hI k hki) (h1 j hJ k hkj)





end stacked
end YM.AnalyticBridge.AnnulusRatioInsertions.Portfolio
