import YM.Planned.PRIMARY_INTEGRAL_295.Glints
/-!
# μ_0 from selected column mean & remμ compared on SAME aperture

Case local finite query hull enough for canonical. Orientation/lift
enters later. No evidence all unreached global rows smooth. Algebra
uses raw exact (negative transpose) affine predictor before Pulse and
norm tests. Costs polynomial u * s where s covers cut tail by caller.
No assuming nonlinear thermal solves implicit. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Glints
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Tropics Cedar Precision Exterior Tree Streets Porous Carrier Bloch
open Progress.StationaryScenes.Green Push.Uniform Matrix Floor Glints.Windows Kelps
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace
variable {E ι κ : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n k : ℕ} {C M σ α u s : ℝ} {f : Side} [Fintype ι] [DecidableEq ι]
namespace Windows
variable {e : κ↪ι} (K:Windows e)
-- scalar centered mean component for every jδ. `b` affine b/t.
def morn (A : Matrix ι ι ℝ) (b:ι→ℝ) (i:κ):= -dotProduct (K.reed A i) b
def remnant (A:Matrix ι ι ℝ) (b ν:ι→ℝ) := A.mulVec ν + b






namespace Glaze
-- Ember δ̂ ensures enough for min comparison with Q. Not estimate all other tags.
variable {h:Aim} {A:E→Matrix ι ι ℝ} {r:ℕ} {l:ι→Site f} (H:K.Glaze h A l k u r)
-- connectivity to C patterns.hub

def payout (k:ℕ) (u:ℝ) := u^2*(2^k*willow u k)


include H

end Glaze

structure Vestal (h:Aim) (A:E→Matrix ι ι ℝ) (b ν:E→ι→ℝ) (l:ι→Site f) (k:ℕ) (u s : ℝ) (r:ℕ) : Prop extends K.Glaze h A l k u r where -- fix syntax
    stamp : mist h r ≤ s
    news i:Ember k (fun x=>ν x i) u
    spark i (j:K.W i): Ember k (fun x=> remnant (A x) (b x) (ν x) j) (u*s)
namespace Vestal
variable {h:Aim} {A:E→Matrix ι ι ℝ} {r:ℕ} {l:ι→Site f} {b ν:E→ι→ℝ} (H:K.Vestal h A b ν l k u s r)

def till (k:ℕ) (u:ℝ):= Glaze.payout k u + (u^2*2^k)*Glaze.payout k u


include H

end Vestal
end Windows
end YM.Planned.PrimaryIntegral295.Glints
