import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Factory
import YM.Push.RELAY_DIFFERENCE.Matching

set_option warningAsError false

/-!
# Fitting and removing the primary part at EACH step

Continuation of a prepared top (E Wdff or lift incl same weight, more
generally ANY Prepared, e.g. equation cylinder). Here one step at a time. No
output common dictionary map for the pure remainders asked even for the
signed estimate. Instead of propagating signed remainders after the fact,
prepare responses to the complement of the ACTUAL primary columns. Only
after continuing to ref will we actually pair the terminal readout.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource
open Function Filter MeasureTheory RG Wilson Lattice Labels Source Bid
open Push.RelayDifference
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {N i p e : ℕ} {C : Family G} {W : Worth}
open Body
variable (H : C.Makes) (h : C.ref e ≤ i) (he : i < N)
include H h he

/-- Names v of calibrated fine/next coarse column with exactly D's primary
coefficients *before* rescaling and propagating D at the step. -/
def attended (D : Inks C e (i+1) p) := fits H (h.trans i.le_succ) he p (coord D)

def rest (D : Inks C e (i+1) p) :=
    D-library C e N p (i+1) (attended H h he D)



/-- A receipt not asking for comparison against any *future* reference
vector. Includes transport and some arbitrary ticket. Crucially, the chosen
response to the complementary ink is preserved here. -/
structure StepOne (D : Inks C e (i+1) p) (E : Inks C e i p) (r : ℝ) : Prop where
  ok : Boots N E
  cap : Shod N E r
  transport : carries N D E
  record : ∃ P : Inks C e i p, E=library C e N p i (attended H h he D)+P ∧ Boots N P ∧
      ∀ c : ℝ,Shod N (rest H h he D) c → count (C:=C) (e:=e) (coord P) ≤ softer C i*c ∧
        Shod N P (softer C i*c)



def charge (C : Family G) (W : Worth) (i : ℕ) (x : C.label e) (u : ℝ) :=
    let L := C.labels.level e; let A := C.S.block i; let K:= W.K (C.path.levels.clock.J (i+1))
    K * L.coeffSize (L.core (vowel L A x)) + barunit A*u
omit H h he in
lemma charge_nn (x : C.label e) {u : ℝ} (hh : 0 ≤ u) : 0 ≤ charge C W i x u := by
  unfold charge; exact add_nonneg (mul_nonneg (zero_le_one.trans (W.prices _)) (coeff_pos _ _))
    (mul_nonneg (by unfold barunit puffs; positivity) hh)


end YM.MultiNext.SignedSource
