import YM.Extra.MULTISOURCE_BOUNDS.Numbered
import YM.Extra.MULTISOURCE_BOUNDS.Singleton
import YM.Further.THRESHOLD_SOURCE_RESTART.Vault
import YM.Push.CORRECTED_COLUMNS.Reprint

/-!
# Charge true source donors

In the restart what is special is **no** dimensional/radius rescaling at
every wire step, and only value order. A positive `divisor` may be retained
in forced marked numbers independently of the unmarked bills; it might need to be bought again through the omission tree when needed. `Income`
is the vertex-level (per input) quantity; it does not assert the weighted or
connected estimate at output. `room` on Capital doesn't renormalize the
comparison: actual coefficients and station identities are unscaled.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.ThresholdSourceRestart
open Function Filter MeasureTheory Wilson RG Lattice Marker Overlay
open Push.Corrected Prepare Width Extra.Multi
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

structure Capital where
  a : ℝ
  unit : ℝ
  b : ℝ
  c : ℝ
  divisor : ℝ
  apos : 0 ≤ a
  unit_pos : 0 ≤ unit
  bpos : 0 ≤ b
  cpos : 0 ≤ c
  room : 0 < divisor
  little : divisor ≤ 1

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] {R : Census V}
variable {P : Rep G n} {w : V → ℝ}
variable (M : Bands R P)

abbrev Owned (K : Capital) (w : V → ℝ) := Prepare.Further M w P.p.B K.a K.unit K.b (K.divisor*K.c)
abbrev Donors (V : Type*) := V ⊕ (ℕ ⊕ (ℕ × ℕ))
def ticket : Donors V → R.Mode := Sum.elim R.fire (Sum.elim M.rays (fun p => M.marks p.1 p.2))
def home : Donors V → Support n := Sum.elim (fun v => {M.origins v}) (Sum.elim M.support (KSite P))

-- Force budget already prices κ^-1. Global unit and body measured in
-- value only (even when H has stronger capacity). No receipts are extracted
-- from blanks. Require the step estimates even on such an input tariff.
structure Income (κ : ℝ) (f : Donors V → ℝ) : Prop where
  bills (i) : 0 ≤ f i
  direct v : f (.inl v) = ‖M.units v‖
  smooth i : ∀ U, ‖masked P.p.threshold (M.support i) (M.H i) U‖ ≤ f (.inr (.inl i))
  seam i (h : masked P.p.threshold (M.support i) (M.H i) = 0) : f (.inr (.inl i))=0
  hard q U : ‖M.entries q.1 q.2 U‖ ≤ κ*f (.inr (.inr q))
  void q (h : M.entries q.1 q.2 = 0) : f (.inr (.inr q))=0

def Capital.total (K : Capital) := Real.exp K.a*K.unit+(K.b+K.c)






end YM.Further.ThresholdSourceRestart
