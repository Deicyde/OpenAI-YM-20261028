import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import YM.Next.WARD_BIN.Clients
import YM.Next.WARD_BIN.Crest

/-!
# Fiscal usability of THESE requests (not a schedule maker!)

Numerical lemmas aimed at feeding RPre costs for this Bin: once (k,P) and
sections fixed, can ask for a *finite* column using Gallery loans, for
any d admitted on a smoothing stage. Including arbitrary further column
increases. Enough after ticket issuance for all Green/tarp uses. After L,
the Quota test too can take losses polynomial in hatβ, with stage-dependent
powers and prefactors and after-L ordered delay.

This doesn't *produce* any scheduled Mark/Q/Volley on rolls chosen this way.
If the demands of those dynamical steps exceed reserves, need to establish a
usable output AGAIN. Don't treat quota proof as proof we can reserve
support exponents after every consecutive same-index step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WardBin.Fiscal
open Function Set Filter MeasureTheory Lattice Wilson RG Source Labels Bid Wheels Crest Supply
open scoped Topology BigOperators Asymptotics
variable {G : Gauge} {C : Family G} {S : Sheet G} {d N p : ℕ}

/-- Compiler database chosen pre-L, read only stale-matched records (Bind
below). Finite profiles for each desired k/P and fixed D; not blanket all
D even at j. -/
structure Fees where
  sect : ℕ → ℕ → ℝ
  score : ℕ → ℕ → ℝ
  mark : ℝ
  mark_pos : 0 < mark




variable (a : ℕ → Fees)

-- Reads only pre-choice profile orders/powers/A



-- increasing columns further has no effect on this revenue


variable {H : Hol G} {F : Frames G} {L : ∀ i,SectionData (F.level i)} (A : Gallery d H F L)
def asks (T : A.Loans) := Fees.mk T.sect T.score T.mark T.live.1



-- One-variable post-L quota, powers of hatβ (OUTPUT/end estimate at i)


/-- Polynomial multiplier at the *output* βhat. Doesn't promise physical kms
factor from step estimates. For fixed L in a stage, courser bootstrap can
charge e.g. powers of L or finite conversion constants into B_j. -/
def surge (C : Family G) (b : ℕ → ℝ) (k : ℕ → ℕ) (i : ℕ) :=
  let T := C.path.levels.clock
  b (T.J (i+1))*(T.hatBeta i)^ k (T.J (i+1))

end YM.WardBin.Fiscal
