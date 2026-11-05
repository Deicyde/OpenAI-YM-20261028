import YM.PertExtension.OrbHessian
import YM.LocalH.Haar
import YM.PertExtension.Interior
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Actual Haar law on the finite product exponential patch. The density before
normalizing denominator includes the common constant as well as the full
non-tree product of Jacobians. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace YM.PertExtension.Chart
open Wilson Lattice Gauge Precision Function Filter Set Metric MeasureTheory MeasureTheory.Measure
open scoped ContDiff Topology Classical BigOperators ENNReal
variable (G : Gauge)(U : Type) [Fintype U]

def expLinks (x : U→G.Color) : U→G.El:=fun i=>G.lieExp (x i)
def tangent := Measure.pi (fun _ : U=> (volume : Measure G.Color))
def physical := Measure.pi (fun _ : U=> G.probHaar)
instance : (tangent G U).IsAddHaarMeasure := by unfold tangent;infer_instance
instance : IsProbabilityMeasure (physical G U) := by unfold physical;infer_instance

variable {G U}
@[fun_prop] lemma expLinks_meas : Measurable (expLinks G U) := by apply measurable_pi_lambda;intro a;exact G.lieExp_cont.measurable.comp (measurable_pi_apply ..)

variable {I K : Type*}
private lemma density_pi [Fintype I] [MeasurableSpace K] (μ : I→Measure K)[∀ i,SigmaFinite (μ i)]
    (f : I→K→ℝ)(hf : ∀ i, Integrable (f i) (μ i))(hv : ∀ i x,0≤f i x) :
   Measure.pi (fun i=> (μ i).withDensity (fun x=> ENNReal.ofReal (f i x))) = (Measure.pi μ).withDensity (fun x=>ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  let W := fun i=>(μ i).restrict (s i)
  have ht : Integrable (fun (x:I→K)=>∏ i,f i (x i)) (Measure.pi W) := Integrable.fintype_prod (f:=f) (μ:=W) (fun i=> (hf i).restrict)
  calc
     _ = ∫⁻ x, ENNReal.ofReal (∏ i,f i (x i)) ∂Measure.pi W := by rw [withDensity_apply _ (MeasurableSet.univ_pi hs),restrict_pi_pi]
     _ = ENNReal.ofReal (∫ x, (∏ i,f i (x i)) ∂Measure.pi W) := (ofReal_integral_eq_lintegral_ofReal ht (Eventually.of_forall fun u=>Finset.prod_nonneg (fun i _=>hv ..))).symm
     _ = ∏ i, ENNReal.ofReal (∫ x, f i x ∂W i) := by rw [integral_fintype_prod_eq_prod (fun (i : I) (x : K)=>f i x), ENNReal.ofReal_prod_of_nonneg fun i _=>integral_nonneg (hv i)]
     _ = _ := by apply Finset.prod_congr rfl; intro i _; rw [withDensity_apply _ (hs i)];exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (Eventually.of_forall <| hv i)

variable (G U) (P : ChartRatio G)
def small := min (P.radius/2) (LocalH.geom_patch G).choose
def chamber (r : ℝ) : Set (U→G.El) := Set.univ.pi fun _=> G.lieExp '' ball 0 r
variable {G U} (P : ChartRatio G)
def fee (x : G.Color) := max (P.scale*P.J x) 0
def jacobian (x :U→G.Color):= ∏ i, fee P (x i)
variable {P} in
lemma jacobian_nonneg (x) : 0≤jacobian (U:=U) P x:= Finset.prod_nonneg (fun i _=>le_max_right ..)
variable {P}

namespace Ratio
variable (R : LocalRatio P)
include R
omit U [Fintype U] in
lemma small_pos : 0<small G P:= lt_min (half_pos R.patch) (LocalH.geom_patch G).choose_spec.1
lemma chamber_open {r}(hr :r ≤ small G P) : IsOpen (chamber G U r):= by
  exact isOpen_set_pi (finite_univ) (fun i _=>((LocalH.geom_patch G).choose_spec.2 r (hr.trans (min_le_right ..))).1)
omit U [Fintype U] in
lemma fee_meas : Measurable (fee P) := (R.borel.const_mul _).max measurable_const
omit U [Fintype U] in
lemma fee_smooth : ContDiffAt ℝ ω (fee P) 0 := by
  have hh : ContDiffAt ℝ ω (fun x=>P.scale*P.J x) 0:= contDiffAt_const.mul (R.germ 0 (mem_ball_self R.patch))
  apply hh.congr_of_eventuallyEq
  have HE : 0 < P.scale*P.J 0 := by rw [R.anchored,mul_one];exact R.scale
  filter_upwards [hh.continuousAt.eventually (isOpen_Ioi.mem_nhds HE)] with x hx using max_eq_left (le_of_lt hx)
omit U [Fintype U] in
lemma feeIntegrable {r}(hr : r ≤ small G P) : IntegrableOn (fee P) (ball 0 r) := by
  have hi := ContinuousOn.integrableOn_compact (μ:=volume) (isCompact_closedBall (0:G.Color) r) (f:=fee P) ?_
  · exact hi.mono_set ball_subset_closedBall
  intro x hx; refine (continuousWithinAt_const.mul ?_).max continuousWithinAt_const
  exact (R.germ x (closedBall_subset_ball ((hr.trans (min_le_left ..)).trans_lt (half_lt_self R.patch)) hx)).continuousAt.continuousWithinAt

variable {r : ℝ} (hr : r≤small G P)
include hr
private lemma link : MeasurePreserving G.lieExp ((volume.restrict (ball 0 r)).withDensity (fun x=> ENNReal.ofReal (fee P x))) (G.probHaar.restrict (G.lieExp '' (ball 0 r))) := by
  have hs : ball (0:G.Color) r ⊆ ball 0 P.radius:=Set.Subset.trans ball_subset_closedBall (closedBall_subset_ball ((hr.trans (min_le_left ..)).trans_lt (half_lt_self R.patch)))
  let S:=G.lieExp '' (ball (0:G.Color) r)
  have hS:=((LocalH.geom_patch G).choose_spec.2 r (hr.trans (min_le_right ..))).1.measurableSet
  have heq x : ENNReal.ofReal (fee P x)=ENNReal.ofReal (P.scale*P.J x):=by by_cases h:0 ≤ P.scale*P.J x
                                                                           · simp [fee,max_eq_left h]
                                                                           simp [fee,ENNReal.ofReal_eq_zero.mpr (not_le.mp h).le, max_eq_right (not_le.mp h).le]
  have hB: G.lieExp ⁻¹' S ∩ ball 0 P.radius= ball 0 r:= by
   ext x;constructor
   · rintro ⟨⟨z,hz,he⟩,hx⟩; exact R.inject (hs hz) hx he ▸ hz
   exact fun hx=>⟨⟨x,hx,rfl⟩,hs hx⟩
  refine ⟨G.lieExp_cont.measurable,?_⟩
  simp_rw [heq]
  calc
     _ = ((volume.restrict (ball 0 P.radius)).withDensity (fun x=>ENNReal.ofReal (P.scale*P.J x))|>.map G.lieExp |>.restrict S) := by
       rw [restrict_map G.lieExp_cont.measurable hS, restrict_withDensity (G.lieExp_cont.measurable hS), Measure.restrict_restrict (G.lieExp_cont.measurable hS), hB]
     _ = _ := by rw [R.actual,Measure.restrict_restrict_of_subset (Set.image_mono hs)]

omit hr in
lemma combined (hr : r<small G P)(hr':0<r) :
   MeasurePreserving (expLinks G U) (((tangent G U).restrict (ball 0 r)).withDensity (fun x=> ENNReal.ofReal (jacobian P x)))
     ((physical G U).restrict (chamber G U r)) := by
  have h₁ := density_pi (I:=U) (fun _=>(volume:Measure G.Color).restrict (ball 0 r)) (fun _=>fee P)
      (fun _=>(feeIntegrable R) hr.le) (fun _ _=>le_max_right ..)
  have h₂:=measurePreserving_pi (ι:=U) _ _ (fun i=>(link R) hr.le)
  simpa only [tangent,physical,ball_pi (0:U→G.Color) hr',Pi.zero_apply,jacobian, chamber,restrict_pi_pi,h₁] using! h₂

omit hr in
lemma jacobian_meas : Measurable (jacobian P (U:=U)) := Finset.measurable_prod _ fun _ _=> (fee_meas R).comp (measurable_pi_apply ..)
omit hr in
lemma chamber_integral (φ : (U→G.El)→ℝ)(hφ : Measurable φ)(hr : r<small G P)(hr':0<r) :
    ∫ x in chamber G U r, φ x ∂physical G U = ∫ x in ball 0 r, jacobian P x*φ (expLinks G U x) ∂tangent G U := by
  rw [← (combined R (U:=U) hr hr').map_eq,integral_map (expLinks_meas (G:=G)).aemeasurable hφ.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ (jacobian_meas R).ennreal_ofReal.aemeasurable (Eventually.of_forall (fun _=>ENNReal.ofReal_lt_top))]
  simp only [fun x : U→_=>ENNReal.toReal_ofReal (jacobian_nonneg (P:=P) x),smul_eq_mul]

omit hr in
lemma jacobian_smooth : ContDiffAt ℝ ω (jacobian P : (U→G.Color)→ℝ) 0 := by
  unfold jacobian; exact contDiffAt_prod fun i _=>(show ContDiffAt ℝ ω (fee P) (Function.eval i (0 : U→_)) from fee_smooth R).comp (f:=fun u : U → G.Color=>u i) _ (contDiffAt_apply ℝ G.Color _ _)

end Ratio

end YM.PertExtension.Chart
