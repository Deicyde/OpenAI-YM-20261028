import YM.Push.BETA_TRANSPORT.Block
import YM.Push.BETA_TRANSPORT.Wilson


/-!
# Normalized pushes through arbitrary finite cutoff histories & their response

`propagate` begins with the *full Wilson weight divided by the top partition*,
multiplying the insertion (one for the vacuum). Recurs exactly down to m, using
the same physical step data and actual input b(m+1) everywhere in that step's
kernel. All b entries may be moved simultaneously. This is a derivative of the
integrals, not a theorem that a lawful description & matching of each perturbed
push or a new physical `History` exists, much less varies differentiably.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG MeasureTheory Gibbs Filter Function
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge} (s : Levels G) (p N : ℕ) (b : ℕ → ℝ) {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  (F : Config G (s.S.side N p) → X)

def propagate (m : ℕ) (hm : m ≤ N) : Config G (s.S.side m p) → X :=
  Nat.decreasingInduction (motive:=fun m _ => Config G (s.S.side m p) → X)
    (fun k _ H => (s.clock.op k p).push (b (k+1)) H) (tilt (prior G (s.S.side N p)) energy (b N) • F) hm

@[simp] lemma propagate_top : propagate s p N b F N le_rfl = tilt (prior G (s.S.side N p)) energy (b N) • F :=
  Nat.decreasingInduction_self ..


def response (r : ℕ → ℝ) (m : ℕ) (hm : m ≤ N) : Config G (s.S.side m p) → X :=
  Nat.decreasingInduction (motive:=fun m _ => Config G (s.S.side m p) → X) (fun k hk H =>
    (s.clock.op k p).push (b (k+1)) H + r (k+1) • pushSlope (s.clock.op k p) (b (k+1)) (propagate s p N b F (k+1) hk))
      (r N • tiltSlope (prior G (s.S.side N p)) energy (b N) • F) hm

variable (r : ℕ → ℝ)
@[simp] lemma response_top : response s p N b F r N le_rfl = r N • tiltSlope (prior G (s.S.side N p)) energy (b N) • F :=
  Nat.decreasingInduction_self ..


def bill (m : ℕ) (hm : m ≤ N) : ℝ := Nat.decreasingInduction (motive:=fun _ _ => ℝ) (fun k _ v =>
    v + ‖r (k+1)‖ * noiseCap (s.clock.op k p)) (‖r N‖ * wilsonCap (s.S.side N p)) hm
@[simp] lemma bill_top : bill s p N r N le_rfl = ‖r N‖ * wilsonCap (s.S.side N p) := Nat.decreasingInduction_self ..



variable {p N F}



variable [CompleteSpace X]
set_option linter.unusedSectionVars false








end YM.Push.BetaTransport
