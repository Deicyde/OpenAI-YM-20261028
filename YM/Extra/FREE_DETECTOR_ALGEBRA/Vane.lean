import YM.Extra.FREE_DETECTOR_ALGEBRA.GradedBasis



set_option warningAsError false

/-! Concrete RCorrected graded Column table. At limiting locations,
or actual marked approximating placements, tracks unit row and column and
connected block costs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest Residue OPE Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix ENNReal

variable {G : Gauge} (C : Family G) (S : Table C.book) {d : ℕ}
local notation "F" => C.labels
local notation "T" => freeTable C.labels

lemma pair_ne (x y : E4) (he : couple x y∈conf _) : x≠y := fun h => (Fin.zero_ne_one (he (show couple x y 0=couple x y 1 from h)))

-- homogeneous basis may be arbitrarily chosen, here is a fitted one

def vane (B : RStage F d) (x y : E4) (he : couple x y∈generic _) : Cells.Columns C S d where
  dim := B.m
  H := table_spin C.labels
  basis := B.b
  realBasis := B.real_i
  initial := B.unit_
  amount := B.m+1
  row i := colPair _ i x y he
  full := by
    let z (i : Fin (B.m+1)) := colPair _ i x y he
    have hc (p) (i) : (z i).tests (freeTable F) B.b p=readsTwo F d x y p (B.b i) := by
      rw [scan_used]; apply congr_arg ((freeTable F).useAt (freeTable F) (couple x y)); ext1 j; fin_cases j <;> rfl
    change Injective fun p i => (z i).tests (freeTable F) B.b p
    simp_rw [hc]; exact scanner_inj F d B.b x y (pair_ne _ _ (generic_conf _ he))

def diagonalGate : E4 := WithLp.toLp 2 (fun _=>1)
lemma vane_possible : couple 0 diagonalGate∈generic _ := by
  intro a i j h; fin_cases i <;> fin_cases j <;> first | rfl | change (0:ℝ)=1 at h; norm_num at h | change (1:ℝ)=0 at h; norm_num at h

variable {C S}







-- Each actual `Trials` mark placement reads the determinant approximant.
-- Avoid any assumption of `Valid.span`, etc.
local notation "gcols" => vane C S










end YM.Extra.FD
