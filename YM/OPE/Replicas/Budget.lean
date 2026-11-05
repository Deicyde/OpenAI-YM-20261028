import YM.OPE.Replicas.ManyBudgets
import YM.OPE.Replicas.Pass
import YM.OPE.Rough.Factory
/-!
# Simultaneous purchases for OPE Lace estimation at any fixed arity
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Lattice RG Wilson MergeProof Source Bid PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Push
variable {G : Gauge} (C : Family G)
set_option quotPrecheck false
structure Package (W : Worth) (r : ℕ → ℕ)
    (D : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) : Prop
    extends TableTickets C W r D where
   productCuts : VelourArity C (renal C.path.levels) r D
end YM.OPE
