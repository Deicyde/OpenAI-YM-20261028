import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel

/-!
# Projecting the absolute sum along the recipe

No evidence here of quantitative `HRGv`. This is the convergence tier. Apply with
actual entry costs; no post-move cancellation certificates needed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson Function Filter Finset
open Push.LogIdentity SectorNext.Reconnect
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side} {p : BudgetPoint}
    {X Y : Plate n}
namespace Roller

variable (T : Roller G p X Y)

/-- At a fixed period. -/
def rides (E : X.Ink G) (u : T.Bit → ℝ) :=
    ∀ i V, Healthy p.threshold (T.shield i.fst) V → ‖T.extra E i V‖ ≤ u i

def credit (E : X.Ink G) := ∃ u,T.rides E u ∧ Summable u

















end Roller
namespace Tape

variable {X Y : Plate n}

def works {X Y : Plate n} : Tape G p X Y → X.Ink G → Prop
  | .clear,_ => True
  | .step T g,E => T.credit E ∧ g.works (T.batch E)

lemma shielded (T : Tape G p X Y) {E : X.Ink G} (h : X.sound E p) :
    Y.sound (T.finalPlate E) p ∧ T.signed.Lands p (T.bill E) ∧
      T.signed.Vouched p (T.bill E) := by
  induction T with
  | @clear X => exact ⟨h, fun i => Empty.elim (show Empty from i), ⟨fun i => Empty.elim (show Empty from i),fun i => Empty.elim (show Empty from i),fun i => Empty.elim (show Empty from i)⟩⟩
  | step T g ih =>
    obtain ⟨hy,hb,hp⟩ := ih (T.sound_batch h)
    exact ⟨hy,Slip.Lands.append (T.hits E) hb, Slip.Vouched.append (T.stamped h) hp⟩


end Tape
end YM.PhysicalNext.PreAtlas
