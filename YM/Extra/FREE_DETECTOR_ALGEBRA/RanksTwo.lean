import YM.Extra.FREE_DETECTOR_ALGEBRA.CrossTerm

set_option warningAsError false

/-! Separate sectors in the pole. Physical interactions not involved. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD.OPE
open Function Filter Set Tensor Analysis Maxwell Wick Residue SphereTest Pair
open scoped Topology ContDiff BigOperators RealInnerProductSpace ComplexOrder

variable {G : Gauge} {n j k h : ℕ}
local notation "L" => Fin (n+1)

def only (P : Sol G.Color j) (Q : Sol G.Color k) (h : ℕ) (v : E4) (x : Points (n+1)) (W : L → WickPol G)
    (I : L→Finset (Slot G)) := ∑ a∈I 0, ∑ i : Fin n, ∑ b∈I i.succ,
      stageTwo x W 0 a i.succ b * residueSingle P Q v h (x 0) (x i.succ) a b







abbrev unitSet := Metric.sphere (0:E4) 1

lemma uq {x} (hx : x∈unitSet) : rr x=1 := by
  unfold rr; have he : ‖x‖ = 1 := by simpa using hx
  rw [he]; norm_num
lemma nonzero_unit {x} (hx : x∈unitSet) : x ≠ 0 := by intro he; subst x; simp at hx






end YM.Extra.FD.OPE
