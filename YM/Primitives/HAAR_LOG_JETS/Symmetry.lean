import YM.Primitives.HAAR_LOG_JETS.Differential

/-!
Symmetries, including outside the chart for the entire **spin function**
(not an assertion that the whole function is the normalized density outside).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.HaarLogJets
open Function Filter Set MeasureTheory NormedSpace LocalH Metric Precision Matrix
open scoped Topology Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace
variable {G : Gauge}

theorem expLine_cont (x : G.Color) : Continuous (fun t : ℝ => exp (back G (t • x))) := by
  letI : NormedAlgebra ℚ (End G) := .restrictScalars ℚ ℝ _
  exact exp_continuous.comp ((back G).continuous.comp (continuous_id.smul continuous_const))

theorem coat_apply (x y : G.Color) : coat G x y = ∫ t in (0:ℝ)..1, G.adjoint (G.lieExp (t • x))⁻¹ y := by
  rw [coat_integral,ContinuousLinearMap.intervalIntegral_apply ((expLine_cont x).intervalIntegrable ..)]
  simp_rw [exp_back]

theorem adjointLine_cont (x y : G.Color) : Continuous (fun t : ℝ => G.adjoint (G.lieExp (t • x))⁻¹ y) := by
  simp_rw [← exp_back]
  exact (expLine_cont x).clm_apply continuous_const

theorem coat_adjoint (u : G.El) (x y : G.Color) : coat G (G.adjoint u x) (G.adjoint u y) = G.adjoint u (coat G x y) := by
  have he (v : G.Color) : G.lieExp (G.adjoint u v) = u * G.lieExp v * u⁻¹ := G.mat_injective <| by
    simp only [G.mat_mul, G.mat_lieExp, G.mat_adjoint,G.exp_conjugate, G.mat_inv]; rfl
  simp_rw [coat_apply,← map_smul,he, ← G.adjoint_mul,show ∀ z : G.El, (u*z*u⁻¹)⁻¹*u=u*z⁻¹ by intro z; group,
    G.adjoint_mul]
  exact (G.adjoint u).toContinuousLinearMap.intervalIntegral_comp_comm ((adjointLine_cont ..).intervalIntegrable ..)

theorem spin_adjoint (u : G.El) (x : G.Color) : spin G (G.adjoint u x) = spin G x := by
  have ht : (coat G (G.adjoint u x)).toLinearMap ∘ₗ G.adjoint u = G.adjoint u ∘ₗ (coat G x).toLinearMap := by
    ext1 y; exact coat_adjoint u x y
  have he : G.adjoint u⁻¹ ∘ₗ G.adjoint u = 1 := by ext1 y; simp [← G.adjoint_mul]
  have hh : LinearMap.det (G.adjoint u) ≠ 0 := by
    intro h
    apply one_ne_zero (α:=ℝ)
    rw [← map_one (LinearMap.det (M:=G.Color) (A:=ℝ)),← he, LinearMap.det_comp,h,mul_zero]
  apply mul_right_cancel₀ hh
  exact (LinearMap.det_comp ..).symm.trans ((congrArg LinearMap.det ht).trans ((LinearMap.det_comp ..).trans (mul_comm ..)))
















theorem ratio_adjoint {A : ChartRatio G} (h : LocalRatio A) {x : G.Color} (hx : x∈ball 0 A.radius) (u : G.El) :
    A.J (G.adjoint u x)=A.J x := by
  rw [Next.SectorChange.contracted h (x:=G.adjoint u x) (by simpa using hx), Next.SectorChange.contracted h hx, spin_adjoint]

end YM.Primitives.HaarLogJets
