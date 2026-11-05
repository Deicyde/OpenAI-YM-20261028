import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Shutter


/-!
# Simultaneous Gaussian rare event purchase

At the actual reference precision, not assuming independence, include
repeated positions and degenerate dimensions. Anchor/fanout for trigger
calculated later. Simple union over coordinate witnesses; product measures
must still use the SAME z,k,Y. This bill with exponent first power of p_β
already enough for optional activity hit test here, not a sharp comparison.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Poll
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask 
open ProbabilityTheory
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators NNReal ENNReal Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {M : ℝ}

abbrev Body (ι : Type) := EuclideanSpace ℝ ι
def sweep (A : Matrix ι ι ℝ) := ProbabilityTheory.multivariateGaussian 0 A

instance probability : IsProbabilityMeasure (sweep A) := by unfold sweep; infer_instance

private lemma shading (hA : A.PosSemidef) (v : Body ι) (t : ℝ) :
    mgf (fun z=> inner ℝ v z) (sweep A) t = Real.exp (dotProduct v.ofLp (A *ᵥ v.ofLp) * t^2 / 2) := by
  let L := innerSL ℝ v
  let W := sweep A
  have X : IsGaussian W := by unfold W sweep; infer_instance
  have ht := IsGaussian.map_eq_gaussianReal (μ:=W) L
  rw [ContinuousLinearMap.integral_comp_id_comm] at ht
  have hV := covarianceBilin_multivariateGaussian (μ:=0) hA v v
  rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id] at hV
  change ProbabilityTheory.covariance L L W=_ at hV
  rw [covariance_self (show AEMeasurable L W from L.measurable.aemeasurable)] at hV
  change ProbabilityTheory.variance L W = dotProduct _ _ at hV
  have he : (∫ x, x ∂W)=0 := by unfold W sweep; simp
  rw [he,map_zero,hV] at ht; rw [show (fun z => inner ℝ v z) = L from rfl]
  change mgf _ W t=_
  rw [mgf_gaussianReal ht,Real.coe_toNNReal,zero_mul,zero_add]
  rw [← hV]; exact variance_nonneg _ _
  exact IsGaussian.integrable_id

private def sound (X : Finset ι) (u : X→Bool) : Body ι := WithLp.toLp 2 fun i =>
    if h : i∈X then (if u ⟨i,h⟩ then -1 else 1) else 0

private lemma audible (X : Finset ι) (u : X→Bool) :
    let v := sound X u
    dotProduct v.ofLp v.ofLp=(X.card:ℝ) := by
  let v := sound X u
  have ht i (hi : i ∈ X) : v i * v i=1 := by unfold v sound; simp only [dif_pos hi]; split <;> norm_num
  have hh : ∑ i∈X, v i * v i=∑ i : ι,v i*v i := by
    apply sum_subset (subset_univ _); intro i _ hi
    simp [v,sound,hi]
  change ∑ i,v i*v i=_; rw [← hh, Finset.sum_congr rfl ht]; simp

private lemma orthant (h : A.PosSemidef) (hv : ∀ v: ι→ℝ, dotProduct v (A *ᵥ v)≤ M*dotProduct v v)
    (X : Finset ι) (u : X→Bool) (t s : ℝ) (hs : 0≤s) :
    (sweep A).real {z : Body ι | ∀ i∈X, t ≤ sound X u i * z i} ≤ Real.exp ((-s*t+M*s^2/2)*X.card) := by
  let v := sound X u; let V := v.ofLp; let F (z : Body ι) := inner ℝ v z
  let μ := sweep A; let m := t*(X.card:ℝ)
  have hh := shading h v s
  change mgf F μ s = _ at hh
  have hg : 0 < mgf F μ s := by rw [hh]; positivity
  calc
    _ ≤ μ.real {z | m ≤ F z} := by
      refine MeasureTheory.measureReal_mono ?_ (measure_ne_top _ _)
      intro z hz; change ∀ i∈X,t≤ v i*z i at hz; change m≤_
      have he : inner ℝ v z=∑ i∈X, v i*z i := by
        rw [real_inner_comm, PiLp.inner_apply]; symm
        simp only [RCLike.inner_apply,starRingEnd_apply,star_trivial]
        refine sum_subset (subset_univ _) ?_; intro i _ hi; simp [v,sound,hi]
      change _ ≤ F z; unfold F; rw [he]; unfold m; simpa [mul_comm t] using (sum_le_sum (f:=fun _=>t) hz)
    _ ≤ _ := by
      refine (measure_ge_le_exp_mul_mgf m hs (mgf_pos_iff.mp hg)).trans ?_
      rw [hh,← Real.exp_add]; apply Real.exp_monotone; apply le_trans (b:= -s*m+M*X.card*s^2/2)
      · have he : dotProduct V (A *ᵥ V) ≤ M*X.card := (hv V).trans_eq (congr_arg (M*·) (audible X u))
        exact add_le_add_right (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (by positivity)) (by norm_num)) _
      unfold m; exact le_of_eq (by ring)

/-- No averaging Y or k inside this call. Price on normalized Gaussian at any
physical covariance with upper Schur cost. X labels arbitrary, volume
independent. -/
lemma rectangle (h : A.PosSemidef) (hv : ∀ v: ι→ℝ, dotProduct v (A *ᵥ v)≤ M*dotProduct v v)
    (X : Finset ι) (t s : ℝ) (hs : 0≤s) :
    (sweep A).real {z : Body ι | ∀ i∈X,t ≤ |z i|} ≤ 2^X.card*Real.exp ((-s*t+M*s^2/2)*X.card) := by
  let F (u : X→Bool) := {z : Body ι | ∀ i∈X, t≤ sound X u i*z i}
  have hg : {z : Body ι | ∀ i∈ X, t ≤ |z i|} ⊆ ⋃ i∈ (univ:Finset (X→Bool)), F i := by
    intro z hz; let u (i : X) := decide (z i.1<0)
    refine Set.mem_iUnion.mpr ⟨u, Set.mem_iUnion.mpr ⟨mem_univ _,?_⟩⟩; intro i hi
    by_cases h : z i<0
    · refine le_trans (hz _ hi) ?_; simp [u,sound,h,abs_of_neg h,hi]
    · refine le_trans (hz _ hi) ?_; simp [u,sound,h,abs_of_nonneg (le_of_not_gt h),hi]
  refine ((MeasureTheory.measureReal_mono hg (measure_ne_top (sweep A) _)).trans (measureReal_biUnion_finset_le _ _)).trans ?_
  apply (Finset.sum_le_sum (fun i _ => orthant h hv X i t s hs)).trans_eq
  simp only [sum_const,nsmul_eq_mul,card_univ]; simp
end YM.ConnectedActivityE6.Poll
