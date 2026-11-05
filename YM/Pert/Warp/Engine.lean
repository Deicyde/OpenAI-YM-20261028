import YM.Pert.Warp.Booth
import YM.Pert.Align.Drivers
/-! Exact same linear driver covariances for the joint Wick rule. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000
set_option maxRecDepth 4000
noncomputable section
namespace YM.Pert.Warp
open Align Lattice Orb MeasureTheory ProbabilityTheory Function Matrix Full
open scoped Topology
variable {N : Side} {G : Gauge} {r d : ℕ}
variable {I : Type} [Fintype I] [DecidableEq I]
def strike (w : I→ℝ) : (I→ℝ) →L[ℝ] ℝ := ∑ i, w i • ContinuousLinearMap.proj i
@[simp] lemma strike_eq (w z : I→ℝ) : strike w z = w ⬝ᵥ z := by unfold strike; simp [dotProduct]

def firsthand (h : ℝ) (x : Site N) (a : Labels.Key G) := strike (kField h x a)
def guest (a : CosKey G d) := (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : CosKey G d=>ℝ) a)
def hall (G : Gauge) (N : Side) (r d : ℕ) (h : ℝ) := mixed (data G N) (auxLaw G d h) r
lemma hall_G (G : Gauge) (N : Side) (r d : ℕ) (h : ℝ) : IsGaussian (hall G N r d h) := let _ := isLaw (G:=G) (n:=N); let _ := auxGaussian (G:=G) (d:=d) h; mix_gaussian _ _ _ -- name collision

def node (h : ℝ) (o : Grid N r) (i : Fin r) (a : CosKey G d) := floating _ _ i (firsthand h (o i) a.val) (guest a)

lemma field_mean (w : Coords G N) : ∫ z : Coords G N, strike w z ∂data G N=0 := by
  letI := isLaw (G:=G) (n:=N)
  unfold strike; simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply]
  rw [integral_finsetSum]
  · simp only [ContinuousLinearMap.proj_apply,smul_eq_mul,integral_const_mul,mean_formula]; simp
  intros i _; exact (IsGaussian.integrable_dual (data G N) (ContinuousLinearMap.proj (i:GIx G N))).smul (w i) -- const_smul
lemma field_entry (i j : GIx G N) : (∫ z : Coords G N,z i * z j ∂data G N) = covarianceM G N i j := by rw [←cov_formula]; unfold covariance; simp only [mean_formula,sub_zero]
lemma field_quad (w v : Coords G N) : (∫ z : Coords G N,strike w z * strike v z ∂data G N)=w ⬝ᵥ (covarianceM G N *ᵥ v) := by
  letI := isLaw (G:=G) (n:=N)
  simp_rw [strike_eq,dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum]
  have h (i j : GIx G N) : Integrable (fun z:Coords G N=>w i * z i * (v j * z j)) (data G N) := by
    let P (f : Coords G N) (i : GIx G N) := Orb.Tame.clm ((ContinuousLinearMap.proj i):Coords G N→L[ℝ] ℝ) |>.scalar_const (f i)
    exact price_tame (data G N) ((P w i).mul (P v j))
  rw [integral_finsetSum _ (fun i _=>integrable_finsetSum _ fun j _=>h i j)]
  simp_rw [integral_finsetSum _ (fun j _=>h ..)]; apply Finset.sum_congr rfl; intro i _; rw [dotProduct,Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
  -- simplify inner form
  simp only [show ∀ z : Coords G N, w i * z i * (v j*z j) = (w i*v j)*(z i*z j) from fun z=>by ring]; rw [integral_const_mul,field_entry]; ring
variable (h : ℝ)
lemma guest_mean (a : CosKey G d) : ∫ z,guest a z ∂auxLaw G d h=0 := Next.SectorChange.Gaussian.cloud_center _ a
lemma guest_quad (a b : CosKey G d) : (∫ z, guest a z * guest b z ∂auxLaw G d h)=link h a.val b.val := by
  let K:= CosKey G d
  let S := @multivariateGaussian K inferInstance inferInstance (0 : EuclideanSpace ℝ K) (shellCov G d h)
  have e (p : K) : Continuous (fun v:EuclideanSpace ℝ K=>v p) := by fun_prop
  have hz (p : K) : Measurable (fun v : EuclideanSpace ℝ K=>v p) := (e p).measurable
  have hi : Measurable (WithLp.ofLp : EuclideanSpace ℝ K→Aux G d) := by fun_prop
  have he (f : Aux G d→ℝ) (hm : Continuous f): (∫ z,f z ∂auxLaw G d h) = ∫ z,f z.ofLp ∂S := integral_map hi.aemeasurable hm.aestronglyMeasurable
  change _=shellCov G d h a b
  rw [he _ (by fun_prop)]; rw [← ProbabilityTheory.covariance_eval_multivariateGaussian (μ:=0) (shellCov_pos (G:=G) (d:=d) h) a b]; unfold covariance
  have eh (q : K): ∫ z,z q ∂S = 0 := (he (fun z=>guest q z) (by fun_prop)).symm.trans (guest_mean h q)
  erw [eh a,eh b]; simp only [sub_zero];rfl

lemma node_center (o : Grid N r) (i : Fin r) (a : CosKey G d) : ∫ z, node h o i a z ∂hall G N r d h = 0 := by
  haveI := isLaw (G:=G) (n:=N)
  haveI := auxGaussian (G:=G) (d:=d) h
  exact float_int _ _ i (field_mean _) (guest_mean h a)
lemma node_wage (o : Grid N r) (i j : Fin r) (a b : CosKey G d) : (∫ z, node h o i a z * node h o j b z ∂hall G N r d h) = (corrected h o i j a.val b.val : ℝ) := by
  haveI := isLaw (G:=G) (n:=N)
  haveI := auxGaussian (G:=G) (d:=d) h
  change (∫ z, floating (Coords G N) (Aux G d) i _ _ z * floating (Coords G N) _ j _ _ z ∂mixed ..) = _
  rw [float_prod (μ:=data G N) (ν:=auxLaw G d h) i j (g1:=guest a) (g2:=guest b) (guest_mean h a) (guest_mean h b), guest_quad h a b, firsthand, firsthand, field_quad]; exact (Complex.ofReal_sub ..).symm
end YM.Pert.Warp
