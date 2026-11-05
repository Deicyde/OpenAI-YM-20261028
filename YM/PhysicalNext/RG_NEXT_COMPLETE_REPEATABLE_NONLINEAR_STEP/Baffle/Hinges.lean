import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plise
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Patch
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Cover

/-!
# Change of variables. From both laws to ONE priced, with explicit relative
 density, translation and Jacobian. No open equivalence across V decisions.

Expose integrands at (Y,f) external tags under authentic unnormalized bill. Also
suitable when V at station and masks flick, through all conditions of Drivable.
Using Heir.tape not changing normalizations; integral L1 verification
 DEFERRED to analytic branch (two equalities individually before taking sum).
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} (V : Config G c)
variable {W E : Support f} {T' : Finset (Tubular f G)} {ζ d A β : ℝ} [Fintype I]
variable (a : Museum F X.x (bareStores S) E Y I) (s : Prices G I) (h : Canary G d A) (hp : 0<β) (hv : Drivable X d A V)

section do_fs

def hang (d β : ℝ) (Y : I→ G.Color) (i:I) := chore X d β V (a.address i) (Y i)
def fast (d β : ℝ) (s : Prices G I) : Prices G I := tape.symm (hang X V a d β (tape s))
def press (d β : ℝ) (i : I) := palm G X.χ d (G.mat (action X V (a.address i))) (peanuts X a X.V β s i)
def pulse (d β : ℝ) := ∏ i, press X V a s d β i

include hp hv
omit [Fintype I] in
private lemma each (i:I) : Bijective (chore X d β V (a.address i)) := by
  let g:= gStep β; let U:= voltage (vary X V) (a.address i); let L:= Eider.fleece G X.χ d (G.mat (action X V (a.address i))); have hh:g≠0:= (inv_pos.mpr (Real.sqrt_pos.mpr hp)).ne'
  have he: Bijective L:= (hv.good (a.address i)).2.1; constructor
  · intro x y h; change g⁻¹ • _ = g⁻¹ • _ at h; apply_fun (fun y:G.Color=>g • y) at h
    rw [smul_inv_smul₀ hh,smul_inv_smul₀ hh] at h
    have hp : g • x=g • y:= add_left_cancel (he.1 (sub_left_inj.mp h)); exact (smul_right_injective _ hh) hp
  intro i'; obtain ⟨v,ha⟩:= he.2 (g • i'+U)
  refine ⟨g⁻¹ • (v-voltage X (a.address i)),?_⟩; change g⁻¹ • (L _-U)=_; rw [smul_inv_smul₀ hh,add_sub_cancel,ha,add_sub_cancel_right,inv_smul_smul₀ hh]

lemma uniquely : Bijective (fast X V a d β) := by
  have he : Bijective (hang X V a d β) := by
    constructor
    · intro i j hh; exact funext fun k=> (each X V a hp hv k).1 (congr_fun hh k)
    intro y; choose v hv using fun i=>(each X V a hp hv i).2 (y i); exact ⟨v,funext hv⟩
  exact tape.symm.bijective.comp (he.comp tape.bijective)

include h
lemma cast :
    let L := (colors (ι:=I) (G:=G)).toContinuousLinearEquiv
    let H := ContinuousLinearMap.pi fun i:I=> ContinuousLinearMap.comp
      (Eider.pax G X.χ d (G.mat (action X V (a.address i))) (peanuts X a X.V β s i)) (ContinuousLinearMap.proj i)
    HasFDerivAt (fast X V a d β) ((L.symm.toContinuousLinearMap.comp H).comp L.toContinuousLinearMap) s := by
  intro L H
  have he : HasFDerivAt (hang X V a d β) H (tape s) := hasFDerivAt_pi.mpr fun i=>(has_chore X h hp V hv (a.address i) (L s i)).comp (f:=fun v:I→G.Color=> v i) _ (hasFDerivAt_apply i (L s))
  exact ((L.symm.hasFDerivAt).comp (L s) he).comp s L.hasFDerivAt

lemma fast_det : (fderiv ℝ (fast X V a d β) s).det=pulse X V a s d β := by
  rw [(cast X V a s h hp hv).fderiv]
  let L := (colors (ι:=I) (G:=G)).toContinuousLinearEquiv; let H := ContinuousLinearMap.pi fun i:I => ContinuousLinearMap.comp
      (Eider.pax G X.χ d (G.mat (action X V (a.address i))) (peanuts X a X.V β s i)) (ContinuousLinearMap.proj i)
  have hh : ((L.symm.toContinuousLinearMap.comp H).comp L.toContinuousLinearMap).det=H.det := by
    rw [ContinuousLinearMap.det]; change LinearMap.det (_∘ₗ _)=_
    exact LinearMap.det_conj H.toLinearMap L.symm.toLinearEquiv
  rw [hh]; unfold H pulse; rw [ContinuousLinearMap.det_pi]; rfl

omit hp h in
lemma marks_up (β : ℝ) : 0< pulse X V a s d β:= Finset.prod_pos fun i _=> ((hv.good (a.address i)).2.2 _).2

lemma travels (v : Prices G I) (f : Prices G I→ℝ) : (∫ t,f t)=∫ t,pulse X V a t d β * f (fast X V a d β t+v) := by
  let g z := fast X V a d β z + v; let μ := volume (α:=Prices G I)
  have hd (z : Prices G I): HasFDerivAt g (fderiv ℝ (fast X V a d β) z) z := ((cast X V a z h hp hv).differentiableAt.hasFDerivAt).add_const v
  have hh : Bijective g:= (Equiv.addRight v).bijective.comp (uniquely X V a hp hv)
  have hr:= integral_image_eq_integral_abs_det_fderiv_smul μ (s:=Set.univ) MeasurableSet.univ (fun x _=> (hd x).hasFDerivWithinAt) hh.1.injOn f
  rw [Set.image_univ, Set.range_eq_univ.mpr hh.2,setIntegral_univ,setIntegral_univ] at hr
  refine hr.trans (integral_congr_ae (ae_of_all _ fun z=>?_)); dsimp only; rw [fast_det X V a z h hp hv, abs_of_pos (marks_up X V a z hv β)]; rfl
end do_fs

section densities
variable [DecidableEq I] (hp' : (lamp6 X a X.V).PosDef)
open Gaussian

-- price explicit. raw E6 normalization (det on μ0 follows cloud_formula).
def chalk (Y : Gaussian.Table (I × G.ColorIndex)) (z y : Prices G I) := Density.replace Y (lamp6 X a X.V) (y-z) z

def reads_map (Y : Gaussian.Table (I × G.ColorIndex)) (d β : ℝ) (v : Prices G I) (z : Prices G I) := pulse X V a z d β * chalk X a Y z (fast X V a d β z+v)

private lemma densityL {ι : Type} [Fintype ι] [DecidableEq ι] {A : Gaussian.Table ι} (hA : A.PosDef) (f : Gaussian.Vec ι→ℝ) : (∫ z,f z ∂ cloud A) = ∫ z, Gaussian.ratio A z*f z := by
  rw [cloud_formula hA,integral_withDensity_eq_integral_toReal_smul (measurable_ratio _).ennreal_ofReal (Filter.Eventually.of_forall fun i=> ENNReal.ofReal_lt_top)]; simp only [ENNReal.toReal_ofReal (ratio_pos hA _).le,smul_eq_mul]

include hp hp' h hv
lemma reels (C : Gaussian.Table (I × G.ColorIndex)) (hC : C.PosDef) (v : Prices G I) (f : Prices G I → ℝ) :
    (∫ t,f t ∂ cloud C)=∫ z, reads_map X V a C d β v z*f (fast X V a d β z+v) ∂ cloud (lamp6 X a X.V) := by
  rw [densityL hC, densityL hp', travels X V a h hp hv v]; refine integral_congr_ae (ae_of_all _ fun z=>?_)
  let y:=fast X V a d β z+v; let Y':= lamp6 X a X.V
  have he : ratio Y' z * chalk X a C z y = ratio C y:= by unfold chalk; rw [Density.ratio_switch _ _ hp', add_sub_cancel]
  dsimp only; unfold reads_map; change pulse X V a z d β * (ratio C y * f y) = ratio Y' z*(pulse X V a z d β * chalk X a C z y*f y); rw [← he]; ring
end densities
end YM.PhysicalNext.Repeat.Baffle
