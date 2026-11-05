import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Weights

/-!
# Applying the local action to the equation packet

All assertions are on the actual torus. No alignment with a blocking level
needed just to use J, even when moving a stencil through a seam. Matrix
readout still refers to the transfer *at the origin*. Translating J means
translating the vector field, including ALL reads, and not recomputing
coefficients.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Equivariance
open Function Filter Labels Lattice Wilson RG Push.CutoffProjectors
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

/-- Keep both conditions in the dependency ledger. Endpoints matter, even if
starting at a zero rotation offset. -/
structure Within (B : Support n) (W : Vectors G n) : Prop where
  depends : LocalOn B W
  backed (U : Config G n) (e : Edge (Site n)) (j : G.ColorIndex) : W U e j ≠ 0 → e.1 ∈ B ∧ e.1 + step e.2 ∈ B



variable {N p d : ℕ} {C : Family G} {E : Packet C d N p}

namespace PhysicalAction
variable (h : PhysicalAction E.weights)
include h

lemma rescaled : PhysicalAction E.X := by
  constructor
  · intro s v
    simp only [Packet.X,LinearMap.comp_apply,scaled_turn]
    exact h.signed s _
  · intro v; simp only [Packet.X,LinearMap.comp_apply,scaled_cw]; exact h.real _
  intro v; exact h.varies _

lemma Jorigin_roll (v : SourceSpace (C.labels.level d)) (s : Signed) (U : Config G (C.side N p)) :
    E.Jorigin (sw _ s v) U = E.Jorigin v (pull s 0 U) :=
  ward_roll _ _ _ s 0 (h.rescaled.signed s v) (h.rescaled.varies v) U

lemma Jorigin_bar (v : SourceSpace (C.labels.level d)) :
    E.Jorigin (cw _ v) = star (E.Jorigin v) := by
  funext U
  change ward (C.S.a N) (C.beta N p) d (E.X (cw _ v)) U = star (ward _ _ _ (E.X v) U)
  rw [h.rescaled.real, ward_star _ _ _ _ (h.rescaled.varies v)]

end PhysicalAction















namespace PhysicalAction
variable (h : PhysicalAction E.weights)
include h







end PhysicalAction
end YM.ProjectorNext.Equivariance
