import YM.Pert.Lattice.Bundles
/-! Real-centered law at each link or auxiliary index; no large-volume limit. -/
set_option autoImplicit false
set_option maxHeartbeats 220000
noncomputable section
namespace YM.Pert.Parity
open MeasureTheory ProbabilityTheory Function Matrix Next.SectorChange.Gaussian Lattice Orb Set
open scoped Topology MatrixOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem multivariate_neg (C : Matrix ι ι ℝ) : (multivariateGaussian 0 C).map (- ·)=multivariateGaussian 0 C := by
  let L := Matrix.toEuclideanCLM (n:=ι) (𝕜:=ℝ) (CFC.sqrt C)
  have h : (stdGaussian (EuclideanSpace ℝ ι)).map (- ·)=stdGaussian (EuclideanSpace ℝ ι) := stdGaussian_map (LinearIsometryEquiv.neg ℝ)
  simp_rw [multivariateGaussian,zero_add]
  change ((stdGaussian (EuclideanSpace ℝ ι)).map L).map (- ·) = (stdGaussian (EuclideanSpace ℝ ι)).map L
  rw [Measure.map_map (by fun_prop : Measurable (- · : EuclideanSpace ℝ ι→_)) L.continuous.measurable]
  conv_rhs => rw [←h,Measure.map_map L.continuous.measurable (by fun_prop : Measurable (- · : EuclideanSpace ℝ ι→_))]
  congr 1;funext; exact (map_neg L _).symm

theorem cloud_neg (C : Matrix ι ι ℝ) : (cloud C).map (- ·)=cloud C := by
  let f := (MeasurableEquiv.toLp 2 (ι→ℝ)).symm
  have ht : (f:EuclideanSpace ℝ ι→ι→ℝ)=WithLp.ofLp := rfl
  simp_rw [cloud,←ht,Measure.map_map (by fun_prop : Measurable (- · : (ι→ℝ)→_)) f.measurable]
  rw [←multivariate_neg C, Measure.map_map f.measurable (by fun_prop : Measurable (- · : EuclideanSpace ℝ ι→_))]
  congr 1; try exact multivariate_neg C
 theorem integral_cloud (C : Matrix ι ι ℝ) (f : (ι→ℝ)→ℂ) (hf : AEStronglyMeasurable f (cloud C)) :
    ∫ x, f (-x) ∂cloud C = ∫ x, f x ∂cloud C := by
   rw [←cloud_neg C] at hf
   conv_rhs=>rw [← cloud_neg C, integral_map (by fun_prop : AEMeasurable (- · : (ι→ℝ) → (ι→ℝ)) (cloud C) ) hf]
end YM.Pert.Parity
