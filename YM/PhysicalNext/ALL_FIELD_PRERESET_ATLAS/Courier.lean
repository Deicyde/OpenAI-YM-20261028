import YM.AnalyticBridge.VERIFIED_RESET_STEP.Trays
import YM.PhysicalNext.ALL_FIELD_PRERESET_ATLAS.Reel


/-!
# Hold the dictionary through the read

Padding not only Reg but Depot (including every possible inspected forced support
format) by `Reconnect.Room.Cipher`. No promise this is all the dormant room a later
consumer (e.g. marks) would need.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PreAtlas
open RG Lattice Wilson Function Filter Finset SectorNext.Reconnect
open AnalyticBridge.VerifiedReset Collection
open Push.LogIdentity Attach
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n : Side}

structure Courier (X : Plate n) (Y : Depot G n) where
  q : ℕ ≃ X.letter ⊕ Room.Cipher n
  k : ℕ ≃ Y.letter ⊕ Room.CipherK n

namespace Courier
variable (X : Plate n) (Y : Depot G n)


variable {X Y} (q : Courier X Y)

/-- The Listing constant with a fixed winding/support/occurrence decoder. -/
def grid : Listing G n :=
  let A := (X.binder (G:=G) 0).enact (Y.binder 0) q.q q.k
  ⟨A.reg,A.forced⟩

def fluid (F : X.Ink G) (K : Y.Ink) : Collection.Source G n :=
  let A := (X.binder F).enact (Y.binder K) q.q q.k
  ⟨A.E,A.K⟩

lemma bind (F : X.Ink G) (K : Y.Ink) : q.grid.read (q.fluid F K) =
    (X.binder F).enact (Y.binder K) q.q q.k := rfl

lemma outgas (p : BudgetPoint) (F : X.Ink G) (K : Y.Ink) (V : Config G n) :
    (q.grid.read (q.fluid F K)).gas p V = ∑' i,Y.sell p K V i := by
  rw [bind, (Room.submits (X.binder F) (Y.binder K) q.q q.k V).2]
  exact tsum_congr fun i => congr_fun (Y.binder_sees p K V) i

lemma outlog (p : BudgetPoint) (F : X.Ink G) (K : Y.Ink) (V : Config G n) :
    (q.grid.read (q.fluid F K)).additive p V = ∑' i,X.maskedLog p F V i :=
    (Room.submits (X.binder F) (Y.binder K) q.q q.k V).1

 -- masks classical decision

end Courier
end YM.PhysicalNext.PreAtlas
