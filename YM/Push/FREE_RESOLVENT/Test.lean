import YM.Push.FREE_RESOLVENT.Flat




/-!
# Tests on downstream interfaces

Check carefully which earlier quality receipts are STILL explicit inputs. In
particular, one doesn't pass in a .Floor etc. to produce the inverse at this
call to Rack. The same object H preserved and read by vacuum uses via
`Attached`. Smoke-test chassis, not claiming availability of Funding or of
period/orientation/root-consistent labels. Frames/hessian/directions from
genuine `Loop`; large-period conditions *post-L*. No spare analytic branch
claims from density equalities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FreeResolvent.Tests
open Lattice Wilson RG Matrix Laurent Bloch Exterior Precision Tree Bid  Filter Function Set Affine
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma frame_pins (T : Forest S.ratio) (v : Key T G) : active T (Precision.frame T v) = Pi.single v 1 := by
  ext i; simp only [active,Precision.frame, Pi.single_apply]; split <;> rename_i H
  · by_cases he : i=v
    · subst v; simp
    rw [if_neg he]; have hx : i.2 ≠ v.2 := fun ht => he (Prod.ext H ht)
    simp [hx]
  rw [if_neg (fun h => H (congr_arg Prod.fst h))]; rfl

lemma checked_loop (T : Forest S.ratio) (B : Bed) (k : S.Choices) (p : Clip) (W : PathData G)
    (h : Prismatic T p W) (he : Comptroller T B p W) : hessian T k p W 0 0=treeMatrix G S T B.metric := by
  ext i j
  rw [Precision.hessian,Matrix.of_apply,tree_hessian S T B k p W h he,frame_pins,frame_pins]
  simp




end YM.FreeResolvent.Tests
