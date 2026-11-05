import YM.RemainderComparison.Rider.Clock
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Logic.Encodable.Basic

/-! Countably many integer-price workloads cover every native workload.
Changing the price receipt preserves the literal input stamp and festival.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.RiderWorkloadEnvelope
open Lattice Wilson RG Marker
open RemainderComparison RemainderComparison.Placement RemainderComparison.Placement.Rider
open scoped Classical

abbrev Code := ℕ × ℕ × ℕ × ℕ × ℕ

def workload (c : Code) : Workload where
  num := c.1
  rank := c.2.1
  extent := c.2.2.1
  price := c.2.2.2.1
  tariff := Nat.cast_nonneg _
  k := c.2.2.2.2

def cover (P : Workload) : Code :=
  (P.num, P.rank, P.extent, ⌈P.price⌉₊, P.k)

theorem cover_data (P : Workload) :
    (workload (cover P)).num = P.num ∧
    (workload (cover P)).rank = P.rank ∧
    (workload (cover P)).extent = P.extent ∧
    (workload (cover P)).k = P.k := ⟨rfl, rfl, rfl, rfl⟩

theorem cover_price (P : Workload) : P.price ≤ (workload (cover P)).price :=
  Nat.le_ceil P.price

def workloadAt (n : ℕ) : Workload :=
  workload ((Encodable.decode (α := Code) n).getD (0, 0, 0, 0, 0))

theorem workloadAt_encode (c : Code) : workloadAt (Encodable.encode c) = workload c := by
  simp only [workloadAt, Encodable.encodek, Option.getD_some]

theorem cofinal (P : Workload) : ∃ n : ℕ,
    (workloadAt n).num = P.num ∧ (workloadAt n).rank = P.rank ∧
    (workloadAt n).extent = P.extent ∧ (workloadAt n).k = P.k ∧
    P.price ≤ (workloadAt n).price := by
  refine ⟨Encodable.encode (cover P), ?_⟩
  rw [workloadAt_encode]
  exact ⟨rfl, rfl, rfl, rfl, cover_price P⟩

variable {G : Gauge} {α : Type*} {q e : ℕ} {A B : ℝ}

def raisePrice (M : Tile G α q e A) (h : A ≤ B) : Tile G α q e B where
  stamp := M.stamp
  bound a := (M.bound a).trans h
  length := M.length
  gauge := M.gauge

theorem raisePrice_stamp (M : Tile G α q e A) (h : A ≤ B) :
    (raisePrice M h).stamp = M.stamp := rfl

theorem raisePrice_read (M : Tile G α q e A) (h : A ≤ B)
    {c : Side} (o : Site c) (a : α) :
    Tile.read (raisePrice M h) o a = Tile.read M o a := rfl

/-- The original atoms, rank, extent, and queried marker counts are unchanged. -/
def coverTile (P : Workload) (M : Tile G α P.rank P.extent P.price) :
    Tile G α (workload (cover P)).rank (workload (cover P)).extent
      (workload (cover P)).price := raisePrice M (cover_price P)

theorem coverTile_stamp (P : Workload) (M : Tile G α P.rank P.extent P.price) :
    (coverTile P M).stamp = M.stamp := rfl

end YM.Integration.RiderWorkloadEnvelope
