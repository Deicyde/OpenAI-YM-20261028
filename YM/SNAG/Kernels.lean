import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import YM.Distribution.Tests
import YM.Spectral.Projection


/-!
# Star algebra ops by integrating VOICE vectors, no assumptions on ‖U t - U s‖

radian normalize once, x index all finite-dimensional inner product spaces.
No Bochner slippage. Schwartz product asserted through explicit equals (no
need complete Schwartz algebra). Large algebra ticket separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SNAG
open Function Set Filter Spectral Boundary Probe MeasureTheory Measure Complex
open scoped Topology NNReal ENNReal InnerProductSpace ComplexOrder BigOperators ContDiff
variable {H : Hilbert} {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] (S : Orbit H X)

abbrev normer (X : Type*) [AddCommGroup X] [Module ℝ X] := ((pref X)⁻¹ : ℝ)
def cut : Probe X →L[ℂ] Probe X := (↑(normer X):ℂ) • Probe.hat
lemma cutting (v : Probe X) (b : X) : cut v b= (normer X:ℂ)*∫ y, plane y (-b)*v y := by
  simp [cut,hat_eq]
lemma light (f : Probe X) (x : X) : (∫ p, plane x p * cut f p)=f x := by
  simp_rw [plane_dot x,cut,_root_.smul_apply,smul_eq_mul,mul_left_comm (plane _ _)]
  rw [integral_const_mul,positiveFourier,Complex.real_smul,← mul_assoc,← ofReal_mul]
  simp only [normer, inv_mul_cancel₀ prepos.ne', ofReal_one,one_mul]

lemma over (f : Probe X) (v : H) : Integrable (fun b => cut f b • S.translation b v) := by
  have hf := ((cut f).continuous.smul (S.moves v)).aestronglyMeasurable (μ := volume)
  apply ((cut f).integrable.norm.mul_const ‖v‖).mono hf
  apply ae_of_all; intro i
  simp [norm_smul,S.unitary]

def listen (f : Probe X) : H.Op := LinearMap.mkContinuous (σ := RingHom.id ℂ) {
    toFun v := ∫ b, cut f b • S.translation b v
    map_add' v w := by simp only [map_add,smul_add]; rw [integral_add (over ..) (over ..)]
    map_smul' c x := by
      simp_rw [map_smul,smul_comm _ c]; rw [integral_smul];rfl
  } (∫ b, ‖cut f b‖) (fun v => show ‖∫ b, cut f b • S.translation b v‖ ≤ _ by
    apply (norm_integral_le_integral_norm _).trans
    simp_rw [norm_smul,S.unitary,integral_mul_const,le_refl])

/-- Integrates Schwartz frequency probes. -/
def send : Probe X →ₗ[ℂ] H.Op where
  toFun := listen S
  map_add' u v := by
    ext1 x
    change (∫ b, _ • S.translation b x)= (∫ b, cut u b • S.translation b x)+(∫ b, cut v b • S.translation b x)
    simp_rw [map_add,_root_.add_apply,add_smul,integral_add (over ..) (over ..)]
  map_smul' c v := by
    ext1 x
    change (∫ b, _ • S.translation b x)=c • ∫ b, cut v b • S.translation b x
    simp_rw [map_smul,_root_.smul_apply,smul_eq_mul,mul_smul, integral_smul]
lemma sending (f : Probe X) (v : H) : send S f v=∫ b, cut f b • S.translation b v := rfl

lemma reversals (f : Probe X) (b : X) : cut (bar f) b=star (cut f (-b)) := by
  rw [cutting,cutting,neg_neg,star_mul']
  congr 1
  · exact (conj_ofReal _).symm
  change _=starRingEnd ℂ _
  rw [← integral_conj]; refine integral_congr_ae (ae_of_all _ fun x => ?_)
  dsimp only; rw [map_mul,bar_at,plane_inverse];rfl

lemma both (f : Probe X) (u v : H) : inner ℂ u (send S (bar f) v)=inner ℂ (send S f u) v := by
  rw [sending, ← inner_conj_symm (send S f u),sending,← integral_inner (over ..), ← integral_inner (over ..),← integral_conj]
  rw [← integral_neg_eq_self (fun b => inner ℂ u (cut (bar f) b • S.translation b v)) volume]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  have he : inner ℂ u (S.translation (-x) v)=inner ℂ (S.translation x u) v := by
    rw [← LinearIsometry.inner_map_map (show _ from { (S.translation x).toLinearMap with norm_map' := S.unitary x })]
    change inner ℂ _ (S.translation x (S.translation (-x) v))=_
    rw [← ContinuousLinearMap.comp_apply,S.sends,add_neg_cancel,S.origin];rfl
  dsimp only; rw [inner_smul_right,inner_smul_right,map_mul,reversals,neg_neg,he,inner_conj_symm];rfl
lemma starify (f : Probe X) : send S (bar f)=star (send S f) := by
  ext1 v; apply ext_inner_left ℂ
  intro u; rw [both]; exact (ContinuousLinearMap.adjoint_inner_right ..).symm

lemma feed (p : X) (u v : Probe X) :
    Integrable (uncurry fun y z : X => plane z (y-p) * v z * cut u y) (volume.prod volume) := by
  let f := fun x : X × X => plane x.2 (x.1-p) * v x.2 * cut u x.1
  have he : Continuous f := by unfold f plane; fun_prop
  apply ((cut u).integrable.norm.mul_prod (v.integrable.norm)).mono he.aestronglyMeasurable
  exact ae_of_all _ fun i => by simp [f, mul_comm]

lemma rolled (u v w : Probe X) (h : ∀ x, w x = u x*v x) (p : X) :
    (∫ y, cut u y * cut v (p-y)) = cut w p := by
  -- use inverse cut identity; signs
  simp_rw [cutting v,cutting w,mul_left_comm (cut u _),integral_const_mul]
  congr 1; simp_rw [← integral_const_mul]
  have he z y : cut u y * (plane z (-(p-y))* v z)=plane z (y-p) * v z * cut u y := by rw [neg_sub,mul_comm]
  simp_rw [he]
  rw [integral_integral_swap (feed p u v)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  have hw y : plane z (y-p)* v z * cut u y= (plane z (-p)*v z)*(plane z y*cut u y) := by
    rw [sub_eq_add_neg,plane_add]; ring
  simp_rw [hw]; rw [integral_const_mul,light,h];ring

/-!
 Integrate links nested. f,g are Schwartz so absolutely conv.
-/
lemma compose {u v w : Probe X} (hw : ∀ x, w x = u x*v x) : (send S u).comp (send S v)=send S w := by
  ext1 x
  rw [ContinuousLinearMap.comp_apply, sending, sending, sending]
  have hf i : cut u i • S.translation i (∫ b, cut v b • S.translation b x) =
      ∫ p : X, (cut u i * cut v (p-i)) • S.translation p x := by
    rw [← ContinuousLinearMap.integral_comp_comm (S.translation i) (over ..),← integral_smul]
    rw [← integral_add_left_eq_self (fun p => (cut u i * cut v (p-i)) • S.translation p x) i]
    refine integral_congr_ae (ae_of_all _ fun j => ?_)
    dsimp only; rw [map_smul,smul_smul,← ContinuousLinearMap.comp_apply,S.sends,add_sub_cancel_left]
  let F := fun (i p : X) => (cut u i * cut v (p-i)) • S.translation p x
  have he : Integrable (uncurry F) (volume.prod volume) := by
    have hf : Continuous (uncurry F) := by
      exact (((cut u).continuous.comp continuous_fst).mul ((cut v).continuous.comp
        (continuous_snd.sub continuous_fst))).smul ((S.moves x).comp continuous_snd)
    apply (integrable_prod_iff hf.aestronglyMeasurable).mpr
    constructor
    · apply ae_of_all
      intro i
      have ht := (hf.comp ((continuous_const (y := i)).prodMk continuous_id)).aestronglyMeasurable (μ := volume)
      have hv := (Probe.ahead i (cut v)).integrable (μ := volume)
      apply (((hv.norm).const_mul ‖cut u i‖).mul_const ‖x‖).mono ht
      exact ae_of_all _ fun j => by simp [F,norm_smul,uncurry,S.unitary]
    simp_rw [F,uncurry, norm_smul,norm_mul,S.unitary,integral_mul_const,integral_const_mul, integral_sub_right_eq_self (fun b => ‖cut v b‖)]
    exact (((cut u).integrable.norm.mul_const _).mul_const _)
  simp_rw [hf]; rw [integral_integral_swap he]
  dsimp only [F]
  simp_rw [integral_smul_const, rolled u v w hw]
end YM.SNAG
