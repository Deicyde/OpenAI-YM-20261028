import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Supra
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Stepped
import YM.TraceExtension.Prom.Hill.TableGate
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Soft.Diana
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Supra for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson RG Next.Rank Tapes Value Perch Filter Set Function Marker Glyph Extraction Market Ship Cells Read Price Dock Camp Station Peak Atlas
open scoped Topology BigOperators Classical
section
variable {G : Gauge} {n : Side} {m k p N v : ℕ} {Z : Demand}
variable {C : Family G} {S : Table C.book} {b : ℝ}

section
variable (hi : k ≤ N) {x : Points v}
variable (Y : Course C N p k) (P : (u : ℕ) → Rep G (C.side u p))
variable (D : Era)
variable (B : Fin v→ (standard C).Tag) (t : Fin v→ C.book.Token)
variable (ho : FitSky C.path.levels b k x)

theorem v_conditionedSky (a : AllowedSky C.path.levels b k) (h : Path_Sky Y P hi b) (hh : Tally (wheelSky C.path.levels k) (C.path.levels.clock.hatBeta k) D m)
    (hw : ∀ u, widthSky C.path.levels b k ≤ u → u ≤ middleSky C.path.levels b k →
      C.path.levels.clock.hatBeta u ∈ Icc (C.path.levels.clock.hatBeta k/2) (C.path.levels.clock.hatBeta k))
    (hp : InstanceSky hi Y P D B t ho m) (hm : v≤ m) (hr : sufficientlySky C B b x k) :
    Ship.estimateSky (P (widthSky C.path.levels b k)) Y hi x (invoiceSky B t ho N p) D.coast.e 1 1 (Ship.allowance C.path.levels m k) := by
  let A := C.path.levels
  let l := middleSky A b k
  let y : l ≤ N := (beforeSky A b k).trans hi
  let T := Ship.yardSky C b hi p
  let M := D.coast
  let s := A.clock.hatBeta k
  let q := A.clock.hatBeta l
  have hc := h l (widerSky A b k) le_rfl
  have hu := hh.stops _ (hw _ (widerSky A b k) le_rfl)
  let J := Peak.Meter C.path.levels hc.budget hu
  obtain ⟨α,β,bα,bβ,H,K,W,hK,hb,hP,hW⟩ := hp.1 hc.budget hu
  have ht : AuroraSky J D.coast.Q Y hi t B ho := by
    refine ⟨α,β,bα,bβ,H,K,W,?_,hK,hb,hP⟩
    refine Peak.warmingSky hu hc.budget hm (fun i => (hW i).2.1) (fun i => (hW i).1) (fun i => (hW i).2.2) (hr ho p N hi)
  have hl := Peak.launchedSky J M.Q Y hi t B ho a hm ht (hc.budget ▸ hu.span) (hc.budget ▸ hu.space)
  apply Perch.coversSky Y P b x m hi hp.2 a hh hw
  have he : spouse s D (l-l)=J.output := by dsimp only [spouse]; rw [Nat.sub_self,pow_zero,one_mul]; rfl
  apply Perch.follows hl
  · exact he.symm.le
  exact hu.reserve.trans_eq (congr_arg (·*w q) he.symm)
end

variable (O : HaarBudget G) {d : ℕ} (X : Columns C S d)

-- eventual allocation from all votes tied path
variable (D : ℕ→ Era) (P : Representatives C X)

end
variable {G : Gauge} {d N p k : ℕ}
variable {C : Family G} {S : Table C.book} (O : HaarBudget G) {X : Columns C S d} (p' : Representatives C X) (b : ℝ)

-- Include lifts explicit even for later usage/ancestry compatibility beyond Purchases scope.

-- extract useful sequence. keep p' & b & X.

end YM.PhysicalNext.InteractingRank.Soft
