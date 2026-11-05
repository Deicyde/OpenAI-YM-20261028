import YM.Next.EXTRACTION.Base
import YM.Push.LOOP_COEFFICIENT.Emit
import YM.Push.LOOP_COEFFICIENT.History.Invoice
import YM.Push.LOOP_COEFFICIENT.Producer.Proceeds

/-!
# Loop certificates on a qualifying common calendar and horizon
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Hist
open Function Matrix Filter Set Lattice Laurent RG Precision Wilson Tree Exterior Bloch Bid Supply Block Producer Gauge
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {S : Sheet G} {R : Rolls S} {V : Protection R} {W : Supply.Delays V} {Y : Supply.Bar W} {Z : Wait Y} {a : Levels G} {M : MapPrices} {B : Horizon a} {N m : ℕ} {O : ChartRatio G} {cost : PostCost R}

abbrev stencil (a : Levels G) (m : ℕ) := (a.clock.op m 0).patch
def staircase (h : Realm M B) (hm : m<N) : Slides (stencil a m) a.clock.kernel (stageTower (B.towers N m)) (B.H N (m+1)) (B.H N m) where
  co := a.S.side m
  fine := a.S.side (m+1)
  size p := (a.clock.op m p).sizes
  grows := (show StrictMono fun p => (a.S.side m p).val from fun _ _ hij => Nat.mul_lt_mul_of_pos_right (a.S.period_strict hij) (a.S.denominator m).pos).tendsto_atTop
  coherent p := h.crossings N m p hm
abbrev certified (B : Horizon a) (O : ChartRatio G) (cost : PostCost R) (N m : ℕ) (F T : PathData G) (α : ℝ) :=
  let j := a.clock.J (m+1); Every (stencil a m) a.clock.kernel (B.towers N m) O (a.params (m+1)).clip (a.params m).clip F T α (cost.η j) (cost.Γ j) (cost.c j) (a.clock.loopCap (m+1))
def Permitted (a : Levels G) (B : Horizon a) (O : ChartRatio G) (cost : PostCost R) := ∀ N m : ℕ,m<N → let X := a.params (m+1); let Y := a.params m
    ∀ {T : PathData G}, Attached (B.H N (m+1)) T → T.Bounds X.clip X.width X.paths (a.clock.loopCap (m+1)) → ∃ α : ℝ, ∃ E : Row (TypeFace 2) (TypeFace 2), |α + G.slopeConstant * Real.log (a.S.block m).val|+1 ≤ X.drift ∧ ∀ {U : PathData G} {cap : ℝ}, Attached (B.H N m) U → U.Bounds Y.clip Y.width Y.paths cap → Attached (B.H N m) (renew E U) ∧ (renew E U).Bounds Y.clip Y.width Y.paths (a.clock.loopCap m) ∧ certified B O cost N m T (renew E U) α




variable (S)


variable {S} {D Q drift : Cost}



end YM.Push.Loops.Hist
