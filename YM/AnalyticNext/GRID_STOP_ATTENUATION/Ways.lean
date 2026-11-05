import YM.AnalyticNext.GRID_STOP_ATTENUATION.Pair
import YM.Next.MULTISOURCE.Mixed
import YM.Push.RELAY_DIFFERENCE.Lanes
import YM.Push.RELAY_DIFFERENCE.TwoSided

set_option warningAsError false

/-! Work simultaneously on all slots of the h system. Use the equivariant
readout in the chosen TransferData. Orient before costing on the dictionary;
no claim that the supplementary remainders themselves are equivariant!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Pair
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Cells
open Push.GridApprox Joint Extraction
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {d k l m h p N : ℕ}

variable (S : Schedule)
def way (h p : ℕ) (i : Site (S.side h p)) := Spin.way (tilesAt S p (le_refl h)) i



variable (C)

def spin {h p : ℕ} (v : C.label d) (i : Site (C.side h p)) := Multi.Fleet.whirl C d (way C.S h p i) v











variable {C}
variable (B : Probe C N p d k) (v : C.label d) (H : C.Makes) (hB : B.Based C.params (C.localSection d) (C.ref d)) (hk : k≤N)

include hB


lemma pale (he : star v=v) : star (tune B v)=tune B v := by
  apply B.terminal.injective; simp only [hB.realForm,tune,B.terminal.apply_symm_apply,he]

include H hk




end YM.AnalyticNext.GridStop.Pair
