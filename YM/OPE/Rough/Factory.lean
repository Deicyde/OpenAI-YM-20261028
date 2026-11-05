import YM.OPE.Columns.Accounts
import YM.MergeProof.North.Economist
import YM.OPE.Rough.Gate
/-!
# Additional inputs for the O(r^(-ε))-loss OPE argument
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open Lattice RG Wilson MergeProof Source Bid PhysicalNext.Repeat.Legato Bandage PhysicalNext.Repeat.Mallow Push
variable {G : Gauge} (C : Family G)
set_option quotPrecheck false
local notation "Q" => C.path.levels

def FramedColumns (W : Worth) := ∀ d N p, C.ref d ≤ N → ∀ m, C.ref d ≤ m → m < N →
    Triangle C.path W m (fun v => ((C.factory d N p).entries (m+1) v).x) (fun v => ((C.factory d N p).entries m v).x)

structure TableTickets (W : Worth) (r : ℕ → ℕ)
    (D : ∀ N p m : ℕ, m < N → GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) : Prop where
   system : Scrim C W (far Q) (waybill Q) (near Q) (renal Q) (fly Q) r D
   accounting : Velour C (renal Q) r D
   columns : FramedColumns C W
   reissue : Fridge C (far Q) (fly Q)
   halos : HaloGate Q
   path : Mix.paidL C
   literal : Ribbons.Created C
   tabs : Stock.Tabs Q

/-- Independent of extraction; proved on the actual constructed carrier. -/
def RoughFactory := ∃ W r D, TableTickets C W r D
end YM.OPE
