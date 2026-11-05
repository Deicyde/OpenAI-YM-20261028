import YM.UVExtension.Rafter.Hales
import YM.UVExtension.Tabernacle.Knots
/-! # Bell.Commuted to Atlas real or complex mark.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Topology Complex Set Lattice RG Push.AbsoluteSums Lamppost Tabernacle
open scoped Topology BigOperators ContDiff Classical
variable {A B D Z:Type}{T:Opening D ℂ}{U:ℝ}
variable (P:Meter.{0,0,0} A B) (r:D→P.Slot)(f:ℂ→Chime P)(h:Bumps T.span f)
variable (hf:∀ d,f (T.call d)=vibe P (r d))(he:∀ d,∃ b,P.MeasureP (r d) b) (hp:∀ z∈T.span,‖f z‖≤U)
include h hf hp he
lemma charmP: Nonempty (Atlas P T r (fun _=> U+U)):=by
   choose w hW using P.awake
   let g(z:ℂ)(i:A)(k:P.test i):= (P.cost (w i) i:ℂ)⁻¹ * f z (P.single i k (w i))
   have hg d i k:g (T.call d) i k= ↑(r d i k):= by unfold g; rw [hf,puts P (he d),Meter.sel, Complex.ofReal_mul, inv_mul_cancel_left₀ (Complex.ofReal_ne_zero.mpr (hW _|>.ne'))]
   have hk(t:P.Finger):Bumps T.span (fun z=> f z t):= fun s p hs hz he=> (show Chime P→L[ℂ]ℂ from BoundedContinuousFunction.evalCLM ℂ t).differentiable.comp_differentiableOn (h s p hs hz he) -- forward.Comp.s
   have hG i k:Bumps T.span (fun z=>g z i k):= fun s p hs hz he=> DifferentiableOn.const_mul (hk _ s p hs hz he) _
   refine ⟨⟨g,hg,hG,fun z hz=> Meter.c_clips _ _ _ (fun i=>?_)⟩⟩
   rw [show Meter.Finger.issue _ _ _= f z i from ?_]; exact ((f z).norm_coe_le_norm i).trans (hp z hz)
   exact T.agrees (fun z=>Meter.Finger.issue P i (g z)) (fun z=> f z i) (P.pollen hG i) (hk i) (fun d=> by rw [hf, puts P (he d)]; exact (P.income _ (fun _ _=> (hg ..).symm)).symm) hz
end YM.UVExtension.Rafter
