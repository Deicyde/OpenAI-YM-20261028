import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import YM.SNAG.Dense

/-!
# Nondegenerate and recovers ORIGINAL group, no atom from fake infinity
-/
set_option autoImplicit false
noncomputable section
namespace YM.SNAG
open Function Set Filter Spectral Boundary Probe MeasureTheory Measure Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators ContDiff
variable {H : Hilbert} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] (S : Orbit H X)

lemma swing {f w : Probe X} (b : X) (h : ∀ x, w x=plane x b*f x) : (S.translation b).comp (send S f)=send S w := by
  have hh (p : X) : cut f p=cut w (b+p) := by
    rw [cutting,cutting]; congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [h,← mul_assoc,← plane_add, show -(b+p)+b=-p by abel] -- -(b+p)+b=...
  ext1 v
  rw [ContinuousLinearMap.comp_apply,sending,sending, ← ContinuousLinearMap.integral_comp_comm (S.translation b) (over ..),
    ← integral_add_left_eq_self (fun p => cut w p • S.translation p v) b]
  simp_rw [map_smul,hh,← ContinuousLinearMap.comp_apply,S.sends]

def panel (f : Probe X) (b : X) (h : HasCompactSupport ⇑f) : Probe X :=
  let y := fun x : X => plane x b*f x
  have he : HasCompactSupport y := HasCompactSupport.mul_left h
  have hu : ContDiff ℝ ∞ (fun x : X => inner ℝ x b) := contDiff_id.inner ℝ contDiff_const
  have hv : ContDiff ℝ ∞ (fun x => plane x b) := ((ofRealCLM.contDiff.comp hu).mul contDiff_const).cexp
  he.toSchwartzMap (hv.mul (f.smooth _))
omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma piece (f : Probe X) (b : X) (h : HasCompactSupport ⇑f) : HasCompactSupport ⇑(panel f b h) :=
  HasCompactSupport.mul_left h

def angle (R : ℝˣ) : X ≃L[ℝ] X := ContinuousLinearEquiv.smulLeft R
omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma hits (x : X) (R : ℝˣ) : angle R x = (R:ℝ) • x := rfl

lemma scaling (t : Probe X) (R : ℝˣ) (hR : 0 < (R:ℝ)) (p : X) :
    cut (along (angle R⁻¹) t) p = (↑((R:ℝ)^Module.finrank ℝ X):ℂ) * cut t ((R:ℝ) • p) := by
  rw [cutting,cutting,mul_left_comm]; congr 1; rw [← Complex.real_smul,
    ← Measure.integral_comp_inv_smul_of_nonneg (R := R) (f := fun x => plane x (-((R:ℝ) • p))* t x) _ hR.le]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only
  rw [along_at,hits, Units.val_inv_eq_inv_val,plane,plane,real_inner_smul_left,inner_neg_right,inner_neg_right,real_inner_smul_right]
  simp [R.ne_zero]

lemma spreads (f : Probe X) (x : H) (R : ℝˣ) (hr : 0<(R:ℝ)) :
    send S (along (angle R⁻¹) f) x = ∫ y, cut f y • S.translation ((R:ℝ)⁻¹ • y) x := by
  rw [sending]
  simp_rw [scaling _ R hr,mul_smul,integral_smul]
  have he y : S.translation y x=S.translation ((R:ℝ)⁻¹ • ((R:ℝ) • y)) x := by rw [inv_smul_smul₀ R.ne_zero]
  simp_rw [show (fun y => cut f ((R:ℝ) • y) • S.translation y x) = _ from funext fun y => congr_arg (cut f ((R:ℝ) • y) • ·) (he y),
      Measure.integral_comp_smul_of_nonneg (R := (R:ℝ)) (hR := hr.le) (f := fun y => cut f y • S.translation ((R:ℝ)⁻¹ • y) x) volume]
  change (R:ℝ)^Module.finrank ℝ X • ((R:ℝ)^Module.finrank ℝ X)⁻¹ • (_:H.space)=_
  rw [smul_inv_smul₀ (by positivity)] -- rfl?

abbrev far (n : ℕ) : ℝˣ := Units.mk0 (↑(n+1):ℝ) (by positivity)
lemma far_pos (n) : 0< (far n:ℝ) := by unfold far; norm_num; positivity
omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma step (p : X) : Tendsto (fun n : ℕ => (((far n:ℝ))⁻¹ • p : X)) atTop (𝓝 0) := by
  have h : Tendsto (fun n => (far n:ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  simpa using (tendsto_inv_atTop_zero.comp h).smul (tendsto_const_nhds (x := p))

def wide (f : Probe X) (n : ℕ) := along (angle (far n)⁻¹) f
omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma broad (f : Probe X) (h : HasCompactSupport ⇑f) (n) : HasCompactSupport ⇑(wide f n) := by
  let F : X ≃ₜ X := (angle (X := X) (far n)⁻¹).toHomeomorph
  apply HasCompactSupport.intro (h.image F.symm.continuous)
  intro x hx; change f (F x)=0; exact image_eq_zero_of_notMem_tsupport (show F x∉tsupport f from fun hf => hx ⟨_,hf,F.symm_apply_apply _⟩)
omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma focus_w (p : X) (f : Probe X) : Tendsto (fun n => wide f n p) atTop (𝓝 (f 0)) :=
  f.continuous.continuousAt.tendsto.comp (step p)

lemma zooms (f : Probe X) (h : f 0=1) (v : H) : Tendsto (fun n : ℕ => send S (wide f n) v) atTop (𝓝 v) := by
  unfold wide; simp_rw [spreads S f v (far _) (far_pos _)]
  have he : v=∫ y, cut f y • v := by
    have ht : (∫ y, cut f y)=1 := by
      simpa only [plane_dot (0:X),plane_zero,one_mul,h] using light f 0
    rw [integral_smul_const,ht,one_smul]
  conv_rhs => rw [he]
  refine tendsto_integral_of_dominated_convergence (fun b => ‖cut f b‖*‖v‖) ?_ ((cut f).integrable.norm.mul_const _) ?_ ?_
  · intro n
    have he := (S.moves v).comp ((continuous_const (y := (far n:ℝ)⁻¹)).smul (continuous_id (X := X)))
    exact ((cut f).continuous.smul he).aestronglyMeasurable
  · exact fun _ => ae_of_all _ fun x => by simp [norm_smul,S.unitary]
  apply ae_of_all; intro x
  have ht := (S.moves v).continuousAt (x := 0) |>.tendsto
  simp_rw [S.origin] at ht
  exact tendsto_const_nhds.smul (ht.comp (step x))
end YM.SNAG
