import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Emitter
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Equivalence
import YM.Axis.Matrix
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Walls
import YM.SectorNext.RECONNECTED_LOCALITY.Missing


/-!
# Transport along the whole emitted tape

This is an EARNINGS option if doing physical orientation estimates. It's not
required of the alphabet used just for the all-field identity or for comparing
emissions through the interval. For this variant explicitly supply a primitive
orientation payroll that covers the **local integrated formulas**, including
emitted answers and their complete supports, not just a symmetry of the
physical input History/`S.push`. No expectation that all these will hold
for any forest presented with arbitrary real entries: even transformations
of complete *identity* sets for publication are extra. Never pair neighbors from
a different history without checking this. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson Function Filter Finset MeasureTheory
open Push.LogIdentity Push.AbsoluteSums Attach Rename
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {n : Side} {G : Gauge}

private abbrev loc (s : Signed) (b : Site n) := StepData.sendSites s b

/-- Carry images of the FULL support. -/
abbrev slid (s : Signed) (b : Site n) := Rename.send (loc s b)

lemma side_slid (s : Signed) (b : Site n) (X : Support n) : slid s b X = X.image (affine s b) := by
  rw [show X.image (affine s b) = X.image (loc s b) from rfl]
  exact Rename.through ..


variable (s : Signed) (b : Site n)

structure Plate.Shift (X : Plate n) (s : Signed) (b : Site n) where
  route : Equiv.Perm X.letter
  located i : X.range (route i)=slid s b (X.range i)
  turns i : (X.label (route i)).site=affine s b (X.label i).site

structure Slip.Shift (X : Slip n) (s : Signed) (b : Site n) where
  route : Equiv.Perm X.letter
  located i : X.reach (route i)=slid s b (X.reach i)

structure Depot.Shift (X : Depot G n) (s : Signed) (b : Site n) where
  route : Equiv.Perm X.letter
  located i : X.range (route i) = slid s b (X.range i)
  owned i : X.need (route i)=slid s b (X.need i)
  takes i V : (X.label (route i)).extraTest V ↔ (X.label i).extraTest (pull s b V)
variable {s b}



def Depot.Shift.sym {X : Depot G n} (e : X.Shift s b) (F : X.Ink) := ∀ i V, F (e.route i) V = F i (pull s b V)







namespace Depot.Shift
variable {X : Depot G n} {P : Slip n} (E : X.Shift s b) (T : P.Shift s b)
    (p : BudgetPoint)



private abbrev J := X.letter ⊕ P.letter


variable (i : J (X:=X) (P:=P))



local notation "Σx" => Finset (X.letter ⊕ P.letter)











end Depot.Shift
end YM.PhysicalNext.PreAtlas
