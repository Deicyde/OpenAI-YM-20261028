import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Diana
import YM.TraceExtension.Prom.Hill.Station
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Diana for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function MeasureTheory Filter Lattice Wilson RG Next.Rank Next.Rank.Tapes Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {S : Table C.book}

variable (F : Cohesion C d) (W : HaarBudget G) (P : Columns C S d)

variable (H : C.Makes)

-- Keep visible mathematical checkpoint. This does NOT assert density Comparison.

-- simultaneous demands before comparison (post-L gates and actual existence of all these inputs on these k stamps)

-- Although Screen needs Ferm at width, keep the ancestral Path to middle
def Path_Sky {k N p}(Y : Course C N p k)(R : (u:ℕ)→Rep G (C.side u p))(hN : k≤N)(b : ℝ):Prop:=
    ∀ u, widthSky C.path.levels b k ≤ u → ∀ h : u ≤ middleSky C.path.levels b k,
      Novice Y u (R u) (h.trans ((beforeSky C.path.levels b k).trans hN))

-- assembly proof
variable (v : Price.Representatives C P)

end YM.PhysicalNext.InteractingRank.Soft
