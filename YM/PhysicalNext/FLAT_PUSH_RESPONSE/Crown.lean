import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Inside
/-!
# Integrated curvature and thermal reward

Only a readiness estimate on the Wilson core (weak-coupling after fixing period).
Includes actual likelihood and our Haar-rotation proof y shift plus COST
caps on supplement. IncomeRay at 0 too. No all-periods estimates after taking
a common growth threshold. Later need even more incl all-scale calibration,
coverage and outputs on genuine Rep.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter WilsonStartup.Change Set Metric Asymptotics MeasureTheory Next.SectorChange.Gaussian
open RG Wilson Precision Lattice  Pressure Work.F05 Tree Matrix 
  
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

namespace IncomeRay
variable {L M : ℝ→ℝ→ℝ} {x y z : ℝ}

-- supplement rays with genuine derivatives not derivative arithmetic through absence





-- only need derivatives at origin including preservation as g varies
lemma exchange {f : ℝ→ℝ} (h : ∀ᶠ y in 𝓝 0,DifferentiableAt ℝ f y) (he : DifferentiableAt ℝ (deriv f) 0) (hp : f 0≠0) : accel (Real.log ∘ f) 0 = accel f 0/f 0 - (deriv f 0)^2/(f 0)^2 := by
  have hh : deriv (Real.log ∘ f) =ᶠ[𝓝 0] fun x=> deriv f x / f x := (h.and
    (h.self_of_nhds.continuousAt.tendsto.eventually (eventually_ne_nhds hp))).mono fun _ hi=> ((hi.1.hasDerivAt).log hi.2).deriv
  unfold accel
  rw [hh.deriv_eq]; exact (he.hasDerivAt.div (h.self_of_nhds.hasDerivAt) hp).deriv.trans (by field_simp)

end IncomeRay

variable {G : Gauge} {m n : Side} {S : StepData m n}
    (B : Forest S.ratio) (k : S.Choices) (u : Bid.Dir G m → AxisChart G B) (p : Clip) (R : PathData G) (w : Bid.Dir G m) {P : ChartRatio G} {r : ℝ}



variable {p R B u}



end YM.PhysicalNext.FlatResponse
