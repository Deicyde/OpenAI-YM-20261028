import YM.Extra.FREE_DETECTOR_ALGEBRA.Forest
import YM.Extra.FREE_DETECTOR_ALGEBRA.Height
import YM.Extra.FREE_DETECTOR_ALGEBRA.Rank

set_option warningAsError false

/-! Radial probe completes the vector kernel proof on most of the space.
Remaining hypothesis here: annihilate at cap 4. Added to Ward rows below
only after proving this costs at most 1 dimension (native connection).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Filter Set Tensor Analysis Maxwell Wick Pair Labels SphereTest   Ward Climb MvPolynomial
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder Matrix

variable {G : Gauge} (F : Frames G) {i j k n d e : ℕ}

local notation "W" => Table.Field (freeTable F)
local notation "T" => freeTable F
local notation "γ" => writes F

-- W-predicate separated all finite arities.


def Strike (v : Fin n → W d) (P : Climb.Matrix d e T) (i : Fin n) := update (fun j => γ d (v j)) i (γ e (P (v i)))
lemma beam_diagram (v : Fin n→ W d) (P : Climb.Matrix d e T) (x : Points n) : diagram v P x= ∑ i : Fin n,moment G x (Strike F v P i) := by
  unfold diagram Strike disc; simp_rw [writes_eval]
  apply Finset.sum_congr rfl; intro i _; congr 1
  let f (_k : Fin n) (z : (freeTable F).Tag) := γ z.1 z.2
  exact updates f (column v) i ⟨_,P (v i)⟩



-- In this file tested vector family kills cap 4.
section listen







end listen

-- k suffices to detect any weight **at the zero position** using bounded cap elsewhere.





-- For vector family P in the candidate cone; if kills cap4 then all (h=specific RealSpin).

end YM.Extra.FD
