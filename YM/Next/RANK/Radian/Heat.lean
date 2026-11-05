import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import YM.Next.RANK.Beamers
import YM.Next.RANK.Bird




/-!
# Continuum normal multiplier

Transform with +2πi in EUCLIDEAN frequencies, standard volume integral
of Green multiplier with fixed Gaussian damping exp(-b |.|²) at ANY nonzero x.
Zero included in the *symbol* even though transform Lebesgue doesn't depend on
it; in period use correct convention. No distribution theorem imported from RG
or claiming UV removal in contact. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Asymptotics Set Real
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform

lemma spaceD : Module.finrank ℝ E4=4:= finrank_euclideanSpace_fin
-- transform shorthand
local notation "𝑒" => Real.exp
def harmon (F : E4→ℂ) (w : E4) := (𝓕 F) (-w)
-- pi-scale chart read

def wave (x y : E4) : ℂ:= (Real.fourierChar (- (inner ℝ y (-x))) : Circle)
def major (u : ℝ) (z : E4) : ℂ := 𝑒 (-u*‖z‖^2)
def blaze (r : ℝ) (z : E4) := Real.exp (-r*‖z‖^2)
lemma major_written (r : ℝ) (z : E4) : major r z=Complex.exp (- (↑r:ℂ) * (‖z‖:ℂ)^2):=by simp [major]
lemma wind (f : E4→ℂ) (x : E4) : harmon f x= ∫ y,wave x y * f y:= by rw [harmon,Real.fourier_eq]; rfl
@[simp] lemma price_wave (x y : E4): ‖wave x y‖=1:= Circle.norm_coe _
lemma major_flight {b : ℝ} (h : 0 < b) (x : E4) : harmon (major b) x=
    (((π/b)^2 * Real.exp (-π^2*‖x‖^2 / b) : ℝ) : ℂ):= by
  have hx:0<(b:ℂ).re:= h
  rw [harmon,show major b=(fun v=>Complex.exp (-(b:ℂ)* (‖v‖:ℂ)^2)) from funext (major_written _),fourier_gaussian_innerProductSpace hx (-x)]
  simp only [norm_neg,spaceD]; norm_cast
  push_cast; norm_num

lemma volume_meet {b : ℝ} (h : 0 < b) : (∫ x:E4,Real.exp (-b*‖x‖^2))=(π/b)^2:= by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm h,spaceD]; norm_num
lemma glowing {b : ℝ} (h : 0 < b): Integrable (major b):= by
  have hx:= GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(b:ℂ)) (by simpa using h) 0 (0:E4)
  simp only [zero_mul,add_zero] at hx; exact hx.congr (Eventually.of_forall fun i=> (major_written ..).symm)

lemma judge (b : ℝ) {z : E4} (h : z≠0) :
    (∫ u : ℝ in Set.Ioi b, Real.exp (-u * ‖z‖^2)) = Real.exp (-b*‖z‖^2) * (‖z‖^2)⁻¹:= by
  have h : 0 < ‖z‖^2:= pow_pos (norm_pos_iff.mpr h) _
  rw [show (fun u=> Real.exp (-u * ‖z‖^2))=(fun u=> Real.exp ((-‖z‖^2)*u)) by ext u; ring_nf, integral_exp_mul_Ioi (by linarith)]
  simp only [neg_div_neg_eq]; ring_nf

def MeasureCore (b : ℝ):= (volume:Measure ℝ).restrict (Set.Ioi b)
lemma heatbelt {b : ℝ} (h : 0 < b) (z : E4): Integrable (fun p : ℝ × E4=> wave z p.2 * major p.1 p.2) ((MeasureCore b).prod volume):= by
  let F (p : ℝ × E4): ℂ:= wave z p.2 * major p.1 p.2
  have hc : Continuous (wave z):= by unfold wave; fun_prop
  have hh: Continuous F:= by unfold F major;fun_prop
  let μ:=MeasureCore b
  have ht : ∀ᵐ x ∂μ,b<x:= ae_restrict_mem measurableSet_Ioi
  have hy r v: ‖F (r,v)‖=Real.exp (-r*‖v‖^2):=by unfold F major; rw [norm_mul,price_wave, one_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]
  refine (integrable_prod_iff hh.aestronglyMeasurable).mpr ⟨ht.mono (fun t ht=> ?_), ?_⟩
  · refine (glowing (h.trans ht)).bdd_mul (hc.aestronglyMeasurable) (Eventually.of_forall (p:=fun i=> ‖wave z i‖ ≤ 1) (by simp))
  have hi:= (integrableOn_Ioi_rpow_iff (s:=(-2:ℝ)) h).2 (by norm_num)
  refine (Integrable.const_mul hi (π^2)).congr (ht.mono ?_)
  intro u hu; change _=∫ v:E4,‖F (u,v)‖; simp_rw [hy]; rw [volume_meet (h.trans hu), div_pow, Real.rpow_neg (h.trans hu|>.le), Real.rpow_two]; ring

lemma bought {u : ℝ} (h : 0 < u) (_b : ℝ) : IntegrableOn (fun x:ℝ=>x^(-2:ℝ)) (Ioi u) volume:= (integrableOn_Ioi_rpow_iff h).2 (by norm_num)
-- Integrate the transformed multiplier on ray. not appealing end Gaussian inversion
lemma radiator {b : ℝ} (h : 0 < b) (z : E4) (hz : z≠0) :
    (∫ u : ℝ in Set.Ioi b,(π/u)^2 *Real.exp (-π^2*‖z‖^2 / u)) = (‖z‖^2)⁻¹*(1- Real.exp (-π^2*‖z‖^2/b)):= by
  let C:= ‖z‖^2; have hC:0 < C:= pow_pos (norm_pos_iff.mpr hz) _
  let F(t : ℝ):= C⁻¹ * Real.exp (-π^2 * C/t);let G(t : ℝ):= (π/t)^2*Real.exp (-π^2*C/t)
  have hf t(ht:0<t):HasDerivAt F (G t) t:= by
    convert! (((hasDerivAt_const (x:=t) _).div (hasDerivAt_id' _) ht.ne').exp.const_mul C⁻¹) using 1
    unfold G; field_simp; simp; ring_nf
  have hu : Integrable G (MeasureCore b):= by
    refine ((bought h b).const_mul (π^2)).mono' (by unfold G; exact (by fun_prop : Measurable (fun t:ℝ=>(π/t)^2*Real.exp (-π^2*C/t))).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (μ:=volume) measurableSet_Ioi] with x hx; have hp : 0<x:= h.trans hx
    unfold G; rw [Real.norm_of_nonneg (by positivity)]; change _ ≤ π^2*x^(-2:ℝ); rw [Real.rpow_neg hp.le, Real.rpow_two]; apply le_trans (b:=(π / x)^2); apply mul_le_of_le_one_right (by positivity); apply Real.exp_le_one_iff.mpr; apply div_nonpos_of_nonpos_of_nonneg _ hp.le; linarith only [show 0 ≤ π^2*C by positivity]; rw [div_pow, div_eq_mul_inv]
  have hV : Tendsto F atTop (𝓝 C⁻¹):= by simpa only [Function.comp_apply,Real.exp_zero, mul_one] using! (Real.continuous_exp.continuousAt.tendsto.comp (tendsto_const_nhds.div_atTop tendsto_id)).const_mul C⁻¹
  change (∫ t in Set.Ioi b,G t)= _; rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto ((hf b h).continuousAt.continuousWithinAt) (fun v hv=> hf v (h.trans hv)) hu hV]
  dsimp only [F,C];ring
end YM.Next.Rank.Radian
namespace YM.Next.Rank.Radian
open MeasureTheory Filter Maxwell Topology Asymptotics Set Real
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform
local notation "𝑒" => Real.exp

-- damped multiplier (zero at singular point) and Fourier computation

def liturgy (b : ℝ) (z : E4) : ℂ := ((Maxwell.normal:ℝ):ℂ) * major b z / ((‖z‖^2:ℝ):ℂ)
lemma chants (b : ℝ) (x y : E4) (hy : y≠0) : wave x y * liturgy b y=((Maxwell.normal:ℝ):ℂ) * (∫ u in Set.Ioi b,wave x y * major u y):= by
  rw [integral_const_mul]; unfold liturgy; unfold major; rw [show (∫ i:ℝ in Set.Ioi b,(Real.exp (-i*‖y‖^2):ℂ)) = (↑(∫ i:ℝ in Set.Ioi b,Real.exp (-i*‖y‖^2)):ℂ) from integral_ofReal,judge b hy]; push_cast; simp only [div_eq_mul_inv]; ring
lemma lit_ae : ∀ᵐ z : E4,z≠0:=ae_iff.mpr (by simp)
lemma none (x : E4) : wave 0 x=1:=by simp [wave]
lemma liturgy_int {b : ℝ} (h : 0<b): Integrable (liturgy b):= by
  haveI : SFinite (MeasureCore b):= (inferInstance : SFinite (volume.restrict (Set.Ioi b)))
  refine ((heatbelt h 0).integral_prod_right.const_mul (↑Maxwell.normal:ℂ)).congr (lit_ae.mono fun i hi=> ?_)
  exact (chants b 0 i hi).symm.trans (by rw [none,one_mul])
lemma chants_h {b : ℝ} (h : 0<b) (z : E4) (hz : z≠0) : harmon (liturgy b) z= (↑(Maxwell.Green z*(1-Real.exp (-π^2*‖z‖^2/b))):ℂ):= by
  have hv := heatbelt h z
  let X (u : ℝ) y:= wave z y * major u y
  haveI : SFinite (MeasureCore b):= (inferInstance : SFinite (volume.restrict (Set.Ioi b)))
  rw [wind,integral_congr_ae (g:=fun i=> (↑Maxwell.normal:ℂ)*∫ u,X u i∂MeasureCore b) (lit_ae.mono (fun i hi=> chants b z i hi)),integral_const_mul,← integral_integral_swap hv]
  have ht : ∀ᵐ v ∂ MeasureCore b,b<v:= ae_restrict_mem measurableSet_Ioi
  rw [integral_congr_ae (ht.mono (fun i hi=> Eq.trans (show ∫ v,X i v= _ from (wind ..).symm) (major_flight (h.trans hi) z))),MeasureCore,show (∫ a:ℝ in Set.Ioi b,(((π/a)^2*Real.exp (-π^2*‖z‖^2 / a):ℝ):ℂ))=(↑(∫ a:ℝ in Set.Ioi b,(π/a)^2*Real.exp (-π^2*‖z‖^2 / a)):ℂ) from integral_ofReal, radiator h z hz]; unfold Maxwell.Green; push_cast; ring

lemma warmth (n : ℕ) (b : ℝ) (h : 0<b) : ∃ C : ℝ, 1 ≤ C ∧ ∀ y : E4, ‖y‖^n * 𝑒 (-b * ‖y‖^2) ≤ C*𝑒 (-(b/2)*‖y‖^2):= by
  have hv := isLittleO_pow_exp_pos_mul_atTop n (show 0<b/2 by linarith only [h]); obtain ⟨g,hG⟩:= eventually_atTop.mp (hv.def zero_lt_one)
  let v:=max 1 g; have ht : 1 ≤ v := le_max_left ..; refine ⟨v^n,one_le_pow₀ ht,fun y=>?_⟩
  let s:= ‖y‖; by_cases hu:v ≤ s
  · have hx : s^n ≤ 𝑒 (b/2*s):=by simpa only [Real.norm_of_nonneg (pow_nonneg (show 0≤s from norm_nonneg y) _),Real.norm_of_nonneg (Real.exp_pos _).le,one_mul] using! hG s ((le_max_right ..).trans hu)
    refine le_trans (b:=𝑒 _ * 𝑒 _) (mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le) ?_
    apply le_trans _ (le_mul_of_one_le_left (Real.exp_pos _).le (one_le_pow₀ ht)); rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; change _ + -b*s^2 ≤ -(b/2) * s^2; nlinarith [mul_le_mul_of_nonneg_left (show s ≤ s^2 by nlinarith) h.le]
  apply mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hu) _) _ (Real.exp_pos _).le (pow_nonneg (zero_le_one.trans ht) _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith only [h]) (sq_nonneg _))

structure Moment (F : E4→ ℂ) : Prop where
  integral : Integrable F
  price : ∀ n : ℕ, Integrable (fun v : E4=> ‖v‖^n*‖F v‖)

lemma lit_norm (b : ℝ) (s : E4): ‖liturgy b s‖=Maxwell.normal * Real.exp (-b*‖s‖^2)/‖s‖^2:= by
  unfold liturgy major;rw [norm_div,norm_mul,Complex.norm_real,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg Maxwell.normal_pos.le, Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_of_nonneg (sq_nonneg _)]
lemma passion {b : ℝ} (h : 0<b) : Moment (liturgy b):= by
  refine ⟨liturgy_int h,fun n=> ?_⟩
  obtain ⟨C,hC,H⟩ := warmth n b h
  refine ((liturgy_int (b:=b/2) (by positivity)).norm.const_mul C).mono' ((continuous_norm.pow n).aestronglyMeasurable.mul (liturgy_int h).aestronglyMeasurable.norm) (Eventually.of_forall (fun i=> ?_))
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)),lit_norm]; change _ ≤ _*‖liturgy _ _‖; rw [lit_norm]
  refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right (H i) (show 0≤ Maxwell.normal/‖i‖^2 from div_nonneg Maxwell.normal_pos.le (sq_nonneg _))).trans_eq ?_) <;> ring
end YM.Next.Rank.Radian
