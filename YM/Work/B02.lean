import YM.Bid.Phase
import YM.Work.B02.Slab


/-!
# B02 -- operator-norm laws of the given Spread

Same Spread, same S and T. AllCopy itself is input here -- no claim
about the other, estimate-producing gates.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.B02
open OS Word

theorem answer : YM.Bid.B02 := by
  intro G L S T P V A _ hT hr _ ht hD hb
  constructor
  · exact hb
  · intro d n v
    rw [show {x | Slab timeAxis d (realize v x)} = region timeAxis d n from
      Set.ext fun x => in_region d v x]
    exact smooth_place P A d ht hT.smooth hr hD hb v
  intro d n v x p hx j
  let b := (p,j)
  change Analysis.D _ _ _ = A.place d (realize (nextLabels P v b) x)
  unfold Analysis.D
  rw [(deriv_place P A d ht hT.smooth hr hD hb v ((in_region d v x).1 hx)).fderiv]
  exact columnD_column P A d v x b
end YM.Work.B02
