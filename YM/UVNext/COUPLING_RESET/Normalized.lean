import YM.Push.BETA_TRANSPORT.Sources
import YM.UVNext.COUPLING_RESET.Reset


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Two scalar currencies from the normalized Wilson/kernel response

Separate UNNORMALIZED v (has a partition term paid in the *original*
volume) and the log-contrast signal for the reset (partition cancels).
Costs follow BETA_TRANSPORT with all finite kernels in the actual order.
Straight lines are comparison of integrals only, with arbitrary level
increments, not assertions about intermediate points being produced by
Directed.advances. Provide a quantitative posterior transport price, and a
primitive differential condition propagating a surplus at one parameter to
the band defect tests when the Fine input is a Wilson prefix. This condition
is on the real lattice integrals even between trajectory points. Need a
much better **error** estimate there than the verified absolute bills in
general! In particular no uniform-in-schedule smallness from those bills.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open MeasureTheory Push.BetaTransport Lattice Wilson RG Shoot Function Filter Set
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} (a : Levels G) (p N : ℕ)

abbrev BetaCurve := ℝ → ℕ → ℝ

def normRead (b : BetaCurve) (m : ℕ) (hm : m ≤ N) (x : ℝ) := normalizedVacuum a p N (b x) m hm

def wilsonRead (b : BetaCurve) (m : ℕ) (hm : m ≤ N) (x : ℝ) (U : Config G (a.S.side m p)) :=
    partition G (a.S.side N p) (b x N) * normRead a p N b m hm x U

variable (b : BetaCurve) {m : ℕ}













def join (b : BetaCurve) (x y z : ℝ) : ℕ → ℝ := fun k => z * (b y k - b x k) + b x k

@[simp] lemma join_zero (x y : ℝ) : join b x y 0 = b x := funext fun i => by simp [join]
@[simp] lemma join_one (x y : ℝ) : join b x y 1 = b y := funext fun i => by simp [join]









def ratioChange (r : ℕ → ℝ) (hm : m ≤ N) (V : Config G (a.S.side m p)) (z : ℝ) :=
    response a p N (b z) (fun _ => 1) r m hm 1 / normRead a p N b m hm z 1 -
    response a p N (b z) (fun _ => 1) r m hm V / normRead a p N b m hm z V










end YM.UVNext.CouplingReset
