import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Flow
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Test
import YM.Push.CUTOFF_PROJECTORS.Spectral

/-!
# Finite readout at the ENCODED x entries; using the transfer-action receipts

Major hypotheses: existence of the Campaign / relevant `ComesFrom`, physical
choice of weights with their local covariance (; e.g. whole
average and `slopes_entries`), and actual termwise regular transport of the
chosen chain. Only sufficient, not a prescription for all of E or assumed
already proved on a history. Do not call on a bin/extracted S.

Use also on BOTH operands of a J-vs-primary comparison at the cutoff.
Does not supply the estimates on that comparison (nor require equation
rank). All costs/convergence hypotheses for use in continuation have to be
additional. Not specifying equivariance of data in unusable padding m
outside `ref d ≤ m ≤ N`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Source Push.CutoffProjectors
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {p N d : ℕ} {C : Family G} {E : Packet C d N p} {S : Finset Cover}

/-- Inputs (in addition to `ComesFrom` and one family). Per needed operation,
not an assumption that readout/projector is equivariant. `weights` include
no charge or column information. `along`, `ordinary` on remainder
presentations before masking (all values). Uses *this* `chain`, not
representatives selected again for the symmetries. Maps on Coefficient labels
index only their regular terms; there is no reindexing of the frame or
unmarked tags. Allow witnessing reindexings per w, require nothing about
forming a group action on the internal names. -/
structure Customs (E : Packet C d N p) : Prop where
  weights : PhysicalAction E.weights
  along (m : ℕ) : C.ref d ≤ m → m ≤ N → ∀ (s : Signed) (v : SourceSpace (C.labels.level d)),
    Nonempty (ListsAlong s 0 (E.chain m v) (E.chain m (sw _ s v)))
  ordinary (m : ℕ) : C.ref d ≤ m → m ≤ N → ∀ v : SourceSpace (C.labels.level d),
    Nonempty (ListsReal (E.chain m v) (E.chain m (cw _ v)))

/-- Actual action on matrices typed as `Model`. Includes even equation labels
of dimension zero, no division by rank. -/
structure ReadsCovariantly {F : Frame G d} (M : Model F) : Prop where
  intertwines (s : Signed) (x : SourceSpace F) : M (sw _ s x) = turn F s (M x)
  ordinary (x : SourceSpace F) : M (cw _ x) = star (M x)

namespace Customs
variable (h : Customs E) (hc : C.Makes) (he : E.ComesFrom S)
include h he hc

lemma matrices (m : ℕ) (hr : C.ref d ≤ m) (hm : m ≤ N) : ReadsCovariantly (E.matrixAt m) := by
  let F := C.labels.level d
  let D := C.localSection d
  let R := C.path.rep N p m
  constructor
  · intro s v
    obtain ⟨P⟩ := h.along m hr hm s v
    have hh : (E.chain m (sw F s v)).density (affine s 0 0) D R = (E.chain m v).density 0 D R ∘ pull s 0 := by
      rw [show affine s (0 : Site (C.side m p)) 0 = 0 by simp [affine]]
      exact charge_roll hc he h.weights m hr hm v s
    exact coord_at_pull D (hc.sections d) 0 (hc.places d m p hr) s 0 (eval_pull hc.wilson N p m hm s 0) hh P
  intro v; obtain ⟨P⟩ := h.ordinary m hr hm v
  exact coord_at_bar D (hc.sections d) 0 (hc.places d m p hr) (charge_star he h.weights m hr hm v) P






end Customs





section Rows
set_option maxRecDepth 4000
/-! Constraint rows use `pair`, conjugate linear on the equation label.
   State explicitly, don't assume that finBasis is somehow fixed by H. -/









end Rows

section Matched









end Matched
end YM.ProjectorNext.Equivariance
