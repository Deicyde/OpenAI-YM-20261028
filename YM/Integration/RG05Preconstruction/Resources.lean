import YM.Integration.ChronPreconstruction.Expenses
import YM.RG05Readout.Offsets.DelayPort
import YM.RG05Readout.Grants.Pinned

/-! Primitive RG05 purchases on the original Bandage.  The larger profile is
fixed after Rolls, before the final delay and before selecting the Run. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.RG05Preconstruction
open RG RG.Supply Lattice Wilson Source Bid
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Legato.Bandage
open scoped Classical

variable {G : Gauge}

def apronProfile {s : Sheet G} (P : Rolls s) (i : ℕ) : ℕ :=
  (i + 2) * (P.L i).val ^ 4

variable {M : Org.Metals G} {P : Rolls M.p} {A : Org.Alloy M P}
  {X : Roost.Factor A} {Y : ℕ → ℝ} {K : Worth}

structure PrimitivePurchase (b : Bandage X Y K) : Prop where
  moved : Cub.Moved b
  minty : Mallow.Minty X.shape (apronProfile P) A.delay
  accord : Mallow.AccordV X.shape (apronProfile P) A.delay

structure ReadoutPurchase (b : Bandage X Y K) : Prop
    extends PrimitivePurchase b where
  steam : Steam (apronProfile P) A.delay
  preMesh (m : ℕ) : ((A.B.a.S.block m).val : ℝ) ≤
    1 + Real.log (2 + Real.log (A.B.a.clock.hatBeta m))
  crossed (i j d : ℕ) (hji : j ≤ i) (hdj : d ≤ j) :
    RG05Readout.Copper.Crossed d i (P.L i) (M.p.profile i) (Y i)
      (RG05Readout.Copper.optics G (M.p.profile j) d)
      (RG05Readout.Copper.ash G d i M.p.profile Y)
      (RG05Readout.Copper.ash G d j M.p.profile Y)
      (RG05Readout.Copper.inverseFuel G d (Y i) (M.p.profile j))
      (RG05Readout.Copper.swing G (M.p.profile i))

structure PrimitiveExtras (Ω : RemainderComparison.Chron.Contemple G)
    (Δ : Daisy.Charity.RG12.Decal G) (b : Bandage X Y K) : Prop
    extends R2I.ChronJoint.Extras Ω Δ b, PrimitivePurchase b

structure Extras (Ω : RemainderComparison.Chron.Contemple G)
    (Δ : Daisy.Charity.RG12.Decal G) (b : Bandage X Y K) : Prop
    extends R2I.ChronJoint.Extras Ω Δ b where
  readout : ReadoutPurchase b

/-- Every old R2I consumer receives the original receipt on this same Bandage. -/
theorem Extras.original {Ω : RemainderComparison.Chron.Contemple G}
    {Δ : Daisy.Charity.RG12.Decal G} {b : Bandage X Y K}
    (h : Extras Ω Δ b) : R2I.Extras Δ b := h.toExtras.original

end YM.Integration.RG05Preconstruction
