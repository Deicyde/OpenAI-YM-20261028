import YM.Cells.Corrected
import YM.Euclid.OtherPlanes
import YM.Phase.Mixture
import YM.Fields.System
import YM.PCalc.Band

/-!
# Data for the Wilson continuum limit
`Final` puts the cutoff, ordered limit, field algebra, phase and Wightman reconstruction on one family and table. The existence theorem is `YM.Nonperturbative.continuum`. The gauge input specifies a compact matrix image and its Lie algebra. The hierarchy includes arity zero.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spec
open Extraction Table Boundary Wilson Cells
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

/-- Cutoff, ordered and generic point limits, hierarchy and corrected field estimates. -/
structure Seed (C : Family G) (f : Order) (S : Table C.book) : Prop where
  cutoff : C.Makes
  ordered : f.Ordered C S
  generic : f.PointLimits C S
  kernel : S.Hierarchy
  copies : CellHyp C f
  corrected : RankWidths C f S

structure Algebra {L : Register G} (S : Table L) where
  derivatives : DiffPlan S
  turns : Rotation S
  energy : Stress S

/-- Field derivatives, rotations, stress tensor and charge laws on the physical quotients. -/
structure Locals {L : Register G} {S : Table L} (X : Algebra S) (h : S.RealSpin) : Prop where
  injection : X.derivatives.Inclusions S
  derivatives : X.derivatives.Derivatives S
  rights : X.derivatives.Orientation h
  spots : X.turns.Laws X.derivatives h
  motion : X.turns.Oriented S
  comparator : Maxwell.Ranks S h
  conserved : Conserved X.derivatives h X.energy
  spin : Tensorial X.turns X.energy
  charges : StressLaws S X.energy X.derivatives.deriv X.turns.lie

structure Materializes {C : Family G} {Z : Table C.book} (X : Algebra Z) (Y : OS.Selection Z) (h : Z.RealSpin) : Prop where
  transport : Locals X h
  phase : OS.Selection.Certificate (P := X.derivatives) X.turns X.energy Y

/-- Continuation of the full and selected Schwinger functions and realization in the selected phase. -/
structure Relativistic {C : Family G} {S : Table C.book} (X : Algebra S) (Y : OS.Selection S) (B A : Contour S) (F : Wightman S)
    (h : S.RealSpin) : Prop where
  allWorld : B.From S
  chosen : A.From (Y.ensemble Y.atPoint)
  qt : F.Realizes (W := A.world) X.turns h

open RG Input Precision Supply Shoot
/-- Stationary and reset witnesses calibrating the steps of the selected Wilson trajectory. -/
def Calibrated (C : Family G) : Prop :=
    ∃ (S : Sheet G) (D : Rolls S) (T : Protection D) (W : Delays T) (Y : Bar W) (I : Wait Y)
        (O : ChartRatio G) (K : MapPrices) (P : PostCost D) (B : Directed G I O K P) (F : ℕ → ∀ p, Trail B.a p),
      B.bake.Stays F ∧ C.path=B.bake.make F ∧ ∀ N m p, m<N → B.Move N m p (F N p m) (F N p (m+1))

/-- Calibration, field algebra, phase selection and relativistic reconstruction on one family and extraction. -/
structure Final (C : Family G) (f : Order) (S : Table C.book) where
  calibration : Calibrated C
  room : Seed C f S
  sector : Algebra S
  α : OS.Selection S
  phase : Materializes sector α room.kernel.spin
  B : Contour S
  A : Contour S
  action : Wightman S
  realization : Relativistic sector α B A action room.kernel.spin

/-- Existence of a Wilson family, extraction and final hierarchy for each allowed gauge group. -/
def CLOSED : Prop := ∀ G : Gauge, G.Simple → ∃ (C : Family G) (f : Order) (S : Table C.book), Nonempty (Final C f S)

/-- Parameter persistence test. No subsequent limit after boundary: these
refinements are at the FAMILY level. -/
def Final.onward {C : Family G} {f : Order} {S : Table C.book} (F : Final C f S) (g : Order) : Final C (f.refine g) S :=
  let h : Seed C (f.refine g) S :=
    { cutoff := F.room.cutoff
      ordered := Order.upon F.room.ordered g
      generic := f.point_retained _ _ F.room.generic g
      kernel := F.room.kernel
      copies := recur F.room.copies g
      corrected d := by
        obtain ⟨X,Y,hy⟩ := F.room.corrected d
        exact ⟨X,Y,Y.refresh f hy g⟩ }
  ⟨F.calibration,h, F.sector, F.α, F.phase, F.B, F.A, F.action, F.realization⟩
end YM.Spec
