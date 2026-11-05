import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Replication
import YM.ProjectorNext.REAL_REFLECTION_COMPRESSION.Tower
import YM.Work.A05.Read

set_option warningAsError false

/-!
# Two species of markers: old fine insertions and new coarse bounded cylinder

Work with actual full signed signal in the physical law
(not numbers from a proposed approximation to a continuum action). Explicit
encoding exponents. Inputs exact; crossing/o offsets use `Tower.replicated`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.RMirror.Net
open Set Filter Function MeasureTheory RG Wilson Lattice Cells Block Tower
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G : Gauge} (H : History G) {k l m p N : ℕ}

abbrev Flags (p m : ℕ) := Site (H.S.side m p)
abbrev beta (N p : ℕ) := H.β N p N

def layers (hm : m ≤ k) (I : Finset (Flags H p m)) (F : Qry H p k) : Qry H p k :=
    fun U => ∏ j∈I,(Tower.floor H hm p).copy j F U







/-- Old source on I with the minus sign for signed substitution. -/
def old (hm : m ≤ N) (F : Qry H p N) (I : Finset (Flags H p m)) : Qry H p N :=
    fun U => (bare (beta H N p) U:ℂ) * layers H hm I (-F) U



/-- Multiplication in the remaining physical variables at k. Marked subsets
include all possible allocations of those sites to old (minus) or new (plus),
never both at one site. Includes the vacuum scalar. -/
def merged (hm : m ≤ k) (hk : k ≤ N) (F : Qry H p N) (A : Qry H p k) (I : Finset (Flags H p m)) : Qry H p k :=
    fun U => ∑ Z∈I.powerset,
      pressed H N p hk (old H (hm.trans hk) F (I\Z)) U * layers H hm Z A U



def charge (l d n : ℕ) : ℂ := ((H.S.a l:ℂ)^d)^n

/-- Signed product in exact physical encoding at scale l. -/
def encoded (d : ℕ) (hm : m ≤ k) (hk : k ≤ N) (h : l ≤ k) (F : Qry H p N) (A : Qry H p k)
    (I : Finset (Flags H p m)) : Qry H p l := fun U => charge H l d I.card * pressed H N p h (merged H hm hk F A I) U






end YM.ProjectorNext.RMirror.Net
