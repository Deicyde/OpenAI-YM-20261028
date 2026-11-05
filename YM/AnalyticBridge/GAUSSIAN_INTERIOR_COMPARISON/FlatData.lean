import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.EXTRACTION.Tails
import YM.Push.FREE_RESOLVENT.Views


/-!
# No-hole and flat alignment on the FreeResolvent side

This part needs no RG program. Keep all the choices even when an uncut
precision is expressible just with `Bed.metric`. Cut **before** inversion
 in any formula that asks for the truncated reference.
-/

noncomputable section
namespace YM.AnalyticBridge.GaussianInterior
open Lattice Wilson RG Pressure Precision Exterior Tree Function Filter
  
open Matrix FreeResolvent
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

namespace FlatData
variable {G : Gauge} {c f : Side} {S : StepData c f}











/-- Every coarse parent has a non-tree edge in its block (could exit
 that block). No assumption of a periodic tree or particular choice. -/
theorem crosses_at (S : StepData c f) (hc : 1 < c.val) (F : Forest S.ratio) (i : Site c) :
    ∃ e : F.Free, S.ratio.parent e.val.1 = i := by
  let g := S.ratio
  let a : Axis := 0
  let t := g.count.val / 2
  let y : Cover := t • step a
  have hy : y ∈ box t := by
    apply (box_iff_layers ..).mpr
    intro j
    unfold layers; by_cases h : j=a <;> simp [y,h]
  let x := g.assemble (i,wrap g.count y)
  have hv : g.parent x = i := g.assemble_parent _
  have hz : g.parent (x+step a) = i+step a := by
    rw [g.parents_hop S.patch.odd_side, hv, if_pos ?_]
    rw [show g.residue x = wrap g.count y from g.assemble_res _, g.half_lift S.patch.odd_side y hy]
    simp [t,y]
  refine ⟨⟨(x,a),fun e => ?_⟩, hv⟩
  exact Affine.View.next_step a hc (hz.symm.trans ((F.trunk_internal e).trans hv))











end FlatData
end YM.AnalyticBridge.GaussianInterior
