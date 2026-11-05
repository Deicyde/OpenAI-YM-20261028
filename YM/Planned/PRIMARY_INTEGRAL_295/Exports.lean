import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Planned.PRIMARY_INTEGRAL_295.Warehouse

/-!
# Entry export theorem

Do not assume output costs on primary columns -- prove with charts
via `builds`. DO assume still other (scheduled independently)
scalar-address Regular and Forced services: respecting masks, true
prices, projection and paid histories. These weaker than PerBlock:
only two fields. Use SAME H etc. Coherent histories in no field.

Costs : exact pre & post in Allow. Witness `_leads` constructed.
Purchasing these prices before L/at trajectories and proving such
source/kernel accounts on an actual H are further upstream (red).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Warehouse
open Function Filter Set Lattice Labels Source RG Wilson Next.Foundations Extra.Histories Bid
open PPX Packing
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {d j t : ℕ} {F : Labels.Frame G d} {A : Hol G}

/-- Two precise external service inputs still needed for `AtomStep`. -/
structure Bystand (T : SectionData F) (H : History G) (N p m : ℕ) (A : Hol G) (η : ℝ) : Prop where
  regular (f : Config G (H.S.side (m+1) p) → ℂ) (b : Support (H.S.side (m+1) p)) (c : ℝ) :
    let R := H.rep N p (m+1)
    let u := η * R.p.mass b c
    RegFit R 0 d A b f → R.p.supBounds 0 b f c → PaidAtom T H N p m A (salary R b f) 0 u u
  forced (f : Config G (H.S.side (m+1) p) → ℂ) (i : ℕ) (c : ℝ) :
    let R := H.rep N p (m+1)
    let u := η * ((R.p.mass (R.activities.forced i).support c) / Real.sqrt (H.levels.clock.forcedAllowance (m+1)))
    SlotFit R 0 i f → 0 ≤ c → (∀ U, ‖f U‖ ≤ c) → PaidAtom T H N p m A (fare R i f) 0 u u

section
variable (T : SectionData F) (hT : T.Sound A) (b : Bid.pop T)
variable {H : History G} {N p m : ℕ} {D : supply H m d} {C η δ : ℝ}




end

abbrev rates (H : History G) (m : ℕ) := Doors.rate (H.S.block m)

/-- Per-block at same calendar and all accepted queries; still precise bills.
Allow fixed by actual localSection; B factors accounted for after L,
other constants pre-L. Use with scheduling obligations; don't freely pick
ink after lengths either. -/
structure Lane (H : History G) (N p m d : ℕ) (D : supply H m d) (C δ : ℝ) : Prop where
  pre : Been H N p m (localSection G d) (hol G) D δ
  prices : Allow H m (localSection G d) (hol G) D (sound G d) (valuation G d) C (rates H m) δ
  bins : Stamp H N p m (localSection G d) (hol G) D δ
  other : Bystand (localSection G d) H N p m (hol G) (rates H m)




end YM.Planned.PrimaryIntegral295.Warehouse
