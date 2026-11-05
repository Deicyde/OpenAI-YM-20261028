import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Slots

/-!
# Between two charts on possibly different periodic input volumes

Conversion principle for actual paired costs, if input tests distinguish
the same links and colours on both sides. Apply with a measurement at a
specified column or connected budget. No assumption that tags, covariances
or fields away from a germ are translates!
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels
open Lattice Wilson RG Function Filter Topology WardBin.Lies Exterior FreeResolvent Affine Mark TestD
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff
variable {G : Gauge} {c c' : Side} {j k : ℕ}

structure Aligned (z : Pins G c j) (w : Pins G c' j) : Prop where
  links t l : edge (z t) = edge (z l) ↔ edge (w t) = edge (w l)
  colors t : (z t).2.2 = (w t).2.2





def recolor {c : Side} (p : OrderedFinpartition j) (z : Pins G c j) (s : Fin p.length → G.ColorIndex) : Pins G c p.length :=
  fun b => repaint p z b (s b)

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Config G c → E} {H : Config G c' → E}
  {z : Pins G c j} {w : Pins G c' j} {U : Config G c} {U' : Config G c'}
  (hF : Germ j F U) (hH : Germ j H U') (h : Aligned z w)
include hF hH h



variable {D : Cost X} {a : Edge (Site c) → X} {x : X} {d δ M : ℝ}


end YM.SelectedOrderedKernels
