import Mathlib.Analysis.Fourier.Convolution
import YM.Next.ROTATIONS.Switch

/-! # Leaving a fixed gap for a nonpointlike axis

Profile with nonnegative opposite Fourier side too. Use convolutions, no Gaussian
normalization. Explicit undamped spectral kernel bounds. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe Metric OS Row
open scoped Topology ContDiff BigOperators Convolution FourierTransform NNReal ENNReal InnerProductSpace ComplexConjugate

private abbrev rconv : ℝ → ℝ := convolution sun sun (ContinuousLinearMap.mul ℝ ℝ) volume
private def circle : Profile :=
  (show HasCompactSupport rconv from HasCompactSupport.convolution _ sun_far.1 sun_far.1).toSchwartzMap
    (HasCompactSupport.contDiff_convolution_right _ sun_far.1 sun.integrable.locallyIntegrable (sun.smooth ⊤))
private lemma cir_plus : Plus circle := by
  intro x; change 0 ≤ ∫ t,sun t*sun (x-t)
  exact integral_nonneg fun t => mul_nonneg (sun_plus t) (sun_plus _)

private lemma product (x : ℝ) : hat (stamp circle) x=(hat (stamp sun) x)^2 := by
  let f := stamp sun
  have he : ⇑(stamp circle)=convolution f f (ContinuousLinearMap.mul ℂ ℂ) volume := by
    funext p
    change Complex.ofReal (∫ t,sun t*sun (p-t)) = ∫ t,(stamp sun t)*(stamp sun (p-t))
    rw [← integral_complex_ofReal]; congr 1; funext t; exact ofReal_mul _ _
  change 𝓕 (⇑(stamp circle)) (collapse x)= (𝓕 (⇑(stamp sun)) (collapse x))^2
  rw [he]; exact (Real.fourier_mul_convolution_eq (f.integrable) (f.integrable) _).trans (pow_two ..).symm

private lemma axis_wave (x : ℝ) : hat (stamp sun) x=hat (stamp sun) (-x) := by
  simp_rw [hat_eq,stamp_at,neg_neg]
  conv_rhs => rw [← integral_neg_eq_self]
  refine integral_congr_ae (ae_of_all _ fun p => ?_); simp only [plane]
  simp [sun_even p]
private lemma ray_real (x : ℝ) : ((hat (stamp sun) x).re:ℂ)=hat (stamp sun) x := by
  have he : starRingEnd ℂ (hat (stamp sun) x)=hat (stamp sun) (-x) := by
    simp_rw [hat_eq,stamp_at,← integral_conj]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [_root_.map_mul,conj_ofReal]; rw [plane_inverse]; simp
  rw [← axis_wave] at he
  have hh := congr_arg im he
  apply Complex.ext (by rfl); simp only [conj_im] at hh; change 0=_; linarith

private def phi (x : ℝ) := ((hat (stamp circle)) x).re
private lemma phi_at (x : ℝ) : ↑(phi x)=hat (stamp circle) x := by
  unfold phi; rw [product,← ray_real,← ofReal_pow]; rfl
private lemma phi_pos (x : ℝ) : 0≤phi x := by
  unfold phi; rw [product,← ray_real,← ofReal_pow]; exact sq_nonneg _
private lemma phi_even (x : ℝ) : phi (-x)=phi x := by unfold phi; rw [product,product,← axis_wave]
private lemma phi_home : phi 0=1 := by
  unfold phi; rw [product]
  have he := jet_at_origin sun 0; simp only [iteratedDeriv_zero,pow_zero,one_mul,sun_mass,Complex.ofReal_one] at he; rw [he]; simp
private lemma hat_width (w : ℝ) (hw : 0<w) (x : ℝ) : hat (stamp (width w circle)) x=↑(phi (w*x)) := by
  rw [phi_at,hat_eq,hat_eq]
  have he := Measure.integral_comp_mul_left (fun b => plane b (-x) * stamp (width w circle) b) w
  apply smul_right_injective ℂ (inv_ne_zero hw.ne')
  rw [abs_of_pos (inv_pos.mpr hw)] at he
  dsimp only
  rw [← he,← integral_smul]; refine integral_congr_ae (ae_of_all _ fun p => ?_)
  change plane (w*p) (-x)*stamp (width w circle) (w*p)= _
  rw [stamp_at,width_at,mul_div_cancel_left₀ _ hw.ne',Complex.ofReal_mul]
  have hx : plane (w*p) (-x)=plane p (-(w*x)) := by simp [plane]; ring_nf
  rw [hx,mul_left_comm]
  rfl

private def shade (u : ℝ≥0) : ContDiffBump (0:ℝ) := ⟨(u:ℝ)+u+1,(u:ℝ)+u+2,by positivity,by linarith⟩
private def tint (u : ℝ≥0) (w : ℝ) : Form :=
  (HasCompactSupport.mul_left (f:=fun x => hat (stamp (width w circle)) x)
    ((shade u).hasCompactSupport.comp_left (show Complex.ofReal 0=0 by norm_cast))).toSchwartzMap (show ContDiff ℝ ∞ _ from
      ((hat (stamp (width w circle))).smooth ⊤).mul ((Complex.ofRealCLM.contDiff).comp (shade u).contDiff))
private lemma tint_at (u w x) : tint u w x=hat (stamp (width w circle)) x * ↑(shade u x) := rfl
private def patch (u : ℝ≥0) (w : ℝ) : Profile := SchwartzMap.postcompCLM Complex.reCLM (port (tint u w))
private lemma projected (u v) (hv : 0<v) : stamp (patch u v)=port (tint u v) := by
  let f := width v circle
  let F := tint u v
  have he x : starRingEnd ℂ (port F x)=port F x := by
    rw [port_eq, Complex.real_smul,map_mul,conj_ofReal,← integral_conj]; congr 1
    rw [← integral_neg_eq_self (fun p : ℝ => (starRingEnd ℂ) _)]; congr 1; funext p
    change starRingEnd ℂ (plane (-p) x * tint u v (-p)) = plane p x*_
    rw [_root_.map_mul,tint_at,tint_at,hat_width _ hv,hat_width _ hv]
    rw [(shade u).neg,mul_neg,phi_even, _root_.map_mul,conj_ofReal,conj_ofReal,plane_dot (-p),plane_dot p,plane_inverse]; simp
  ext1 x
  change ((port F x).re:ℂ)=port F x
  have H := congr_arg im (he x)
  apply Complex.ext (by rfl); simp only [conj_im] at H; change 0=_; linarith
private lemma cut (u v) (hv : 0<v) (x : ℝ) : hat (stamp (width v circle-patch u v)) x= ↑((1-shade u x)*phi (v*x)) := by
  simp only [map_sub,projected u v hv,travels,_root_.sub_apply, tint_at,hat_width v hv,Complex.ofReal_mul,Complex.ofReal_sub,Complex.ofReal_one]; ring

def civic := circle
def remote (u : ℝ≥0) (w : ℝ) := patch u w
lemma civic_plus : Plus civic := cir_plus
lemma remote_gap (u : ℝ≥0) (w : ℝ) (hw : 0<w) (t : ℝ) (hp : hat (stamp (width w civic-remote u w)) t ≠0) :
    ((u+u:ℝ≥0):ℝ) ≤ |t| := by
  by_contra! hh; apply hp
  unfold remote civic; rw [cut u w hw]
  have he : shade u t=1 := (shade u).one_of_mem_closedBall (by
    apply mem_closedBall.mpr
    rw [dist_zero_right,Real.norm_eq_abs]; refine hh.le.trans ?_
    rw [NNReal.coe_add]; simp [shade])
  simp [he]

private lemma phi_int : Integrable phi := (hat (stamp circle)).integrable.re
private lemma phi_bound : ∃ C : ℝ, ∀ t, phi t ≤ C :=
  ⟨SchwartzMap.seminorm ℝ 0 0 (hat (stamp circle)), fun _ => (Complex.re_le_norm _).trans ((hat (stamp circle)).norm_le_seminorm _ _)⟩
lemma remote_cost (u : ℝ≥0) : ∃ C : ℝ,0≤C ∧ ∀ (w : ℝ),0<w → ∀ t : ℝ, ‖remote u w t‖ ≤ C := by
  obtain ⟨C,hC⟩ := phi_bound; have hp : 0≤C := (phi_pos 0).trans (hC 0)
  let L := C*∫ x : ℝ, shade u x
  have hx t w (hw : 0<w) : ‖∫ p, plane p t*tint u w p‖ ≤ L := by
    unfold L; rw [← integral_const_mul]; refine norm_integral_le_of_norm_le ((shade u).integrable (μ:=volume) |>.const_mul C) (ae_of_all _ fun p => ?_)
    change ‖plane p t * _‖ ≤ C*shade u p
    rw [norm_mul,plane_norm,one_mul,tint_at,hat_width w hw]
    rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (shade u |>.nonneg),Real.norm_of_nonneg (phi_pos _)]
    exact mul_le_mul_of_nonneg_right (hC _) ((shade u).nonneg)
  have hL : 0 ≤ L := (norm_nonneg _).trans (hx (0:ℝ) 1 zero_lt_one)
  refine ⟨(pref ℝ)⁻¹ * L,mul_nonneg (inv_pos.mpr prepos).le hL,fun w hw t => ?_⟩
  rw [show ‖remote u w t‖=‖port (tint u w) t‖ from (by
    rw [← projected u w hw,stamp_at,Complex.norm_real]; rfl),port_eq,norm_smul,Real.norm_of_nonneg]
  · exact mul_le_mul_of_nonneg_left (hx _ w hw) (inv_pos.mpr prepos).le
  exact (inv_pos.mpr prepos).le

private def leg (u : ℝ≥0) (w E t : ℝ) := Real.exp (-|t| *E)*((1-shade u t)*phi (w*t))
private lemma leg_nn (u w E t) : 0 ≤ leg u w E t := mul_nonneg (Real.exp_pos _).le
  (mul_nonneg (sub_nonneg.mpr (shade u |>.le_one)) (phi_pos _))
private lemma termed (u w E t) (h : 0<w) : (leg u w E t:ℂ)=damped 1 (stamp (width w civic-remote u w)) E t := by
  simp only [civic, remote, damped,side,ite_self,one_mul,cut u w h, leg]; push_cast; rfl
private lemma leg_int (u w E) (h : 0<w) (hp : 0 ≤ E) : Integrable (leg u w E) := by
  have ht := (damped_fiber 1 (stamp (width w civic-remote u w)) hp).re
  simp_rw [← termed u w E _ h] at ht; exact ht
private lemma covered (u w E) (h : 0<w) (_ : 0 ≤ E) :
    (Lap 1 (stamp (width w civic-remote u w)) E).re=∫ t,leg u w E t := by
  unfold Lap
  simp_rw [← termed u w _ _ h]; rw [integral_complex_ofReal]; rfl
lemma remote_sign (u : ℝ≥0) (w : ℝ) (hw : 0<w) (i : Axis) (p : E4) (hp : 0 ≤ p i) :
    0≤ Reel i (width w civic-remote u w) p := by rw [Reel,covered u w _ hw hp]; exact integral_nonneg fun _ => leg_nn ..
lemma remote_top (u : ℝ≥0) : ∃ C : ℝ,0≤C ∧ ∀ w : ℝ, 0<w → ∀ E : ℝ,0 ≤ E →
    (Lap 1 (stamp (width w civic-remote u w)) E).re ≤ C*w⁻¹*Real.exp (-((u+u:ℝ≥0):ℝ)*E) := by
  let J := ∫ t,phi t
  have hJ : 0 < J := by
    have hp := integral_pos_iff_support_of_nonneg (f:=phi) (μ:=volume) (fun t => phi_pos t) phi_int
    apply hp.mpr
    refine IsOpen.measure_pos (μ:=volume) ?_ ⟨0,fun h => one_ne_zero (phi_home.symm.trans h)⟩
    exact isClosed_eq (Complex.continuous_re.comp (hat (stamp circle)).continuous) (continuous_const (y:=0)) |>.isOpen_compl
  refine ⟨J,hJ.le,fun w hw E h => ?_⟩
  let v : ℝ := Real.exp (-((u+u:ℝ≥0):ℝ)*E)
  rw [covered u w E hw h]
  have ht := Measure.integral_comp_mul_left phi w; rw [abs_of_pos (inv_pos.mpr hw)] at ht
  change _ ≤ J*w⁻¹*v
  calc
    _ ≤ ∫ t : ℝ,v*phi (w*t) := by
      have he : Integrable (fun t : ℝ => phi (w*t)) := Integrable.of_integral_ne_zero (by
        rw [ht]; exact (mul_pos (inv_pos.mpr hw) hJ).ne')
      apply integral_mono (leg_int u w E hw h) (he.const_mul v)
      intro t
      unfold leg
      by_cases hz : ((u+u:ℝ≥0):ℝ) ≤ |t|
      · rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ (phi_pos _)
        refine (mul_le_of_le_one_right (Real.exp_pos _ |>.le) ?_).trans (Real.exp_le_exp.mpr ?_)
        · linarith [(shade u).nonneg (x:=t)]
        exact mul_le_mul_of_nonneg_right (neg_le_neg hz) h
      have hi := mt (remote_gap u w hw t) hz
      rw [not_not] at hi; unfold civic remote at hi; rw [cut u w hw, Complex.ofReal_eq_zero] at hi; rw [hi,mul_zero]
      exact mul_nonneg (Real.exp_pos _ |>.le) (phi_pos _)
    _ = _ := by rw [integral_const_mul,ht]; change v*(w⁻¹*J)=_; ring
/-- All dyads at once above and through zero. Placement cost kept. -/
lemma remote_base (u : ℝ≥0) : ∃ c v : ℝ,0<c ∧ 0<v ∧ ∀ w : ℝ,0<w → w≤v → ∀ E : ℝ,0≤E → E≤1 →
    c/(E+w) ≤ (Lap 1 (stamp (width w civic-remote u w)) E).re := by
  let R := (shade u).rOut
  have hr : 0<R := (shade u).rOut_pos
  have hp : ContinuousAt phi 0 := (Complex.continuous_re.comp (hat (stamp circle)).continuous).continuousAt
  obtain ⟨a,ha,hA⟩ := Metric.mem_nhds_iff.mp (hp.eventually (lt_mem_nhds (show 1/2<phi 0 by rw [phi_home]; norm_num)))
  let δ := a/3
  have hd : 0<δ := by unfold δ; positivity
  let c := Real.exp (-(R+δ))/2
  have hc : 0<c := by unfold c; positivity
  refine ⟨c*δ,δ/R,mul_pos hc hd,div_pos hd hr,fun w hw ht E hE h => ?_⟩
  rw [covered u w E hw hE]
  have he : 0<E+w := by linarith
  let L : Set ℝ := Ioc R (R+δ/(E+w))
  calc
    _ = ∫ _ in L,c := by
      rw [setIntegral_const]; unfold L
      rw [Real.volume_real_Ioc,add_sub_cancel_left,max_eq_left (by positivity),smul_eq_mul]; ring
    _ ≤ ∫ t in L, leg u w E t := by
      refine setIntegral_mono_on (integrableOn_const (ne_of_lt ?_)) (leg_int u w E hw hE).integrableOn measurableSet_Ioc ?_
      · exact lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self) (isCompact_Icc.measure_lt_top (μ:=volume))
      intro t hL
      have hz := (show t∈ Ioc R _ from hL).1
      have hl := (show t∈ Ioc _ (R+δ/(E+w)) from hL).2
      have hT : 0<t := hr.trans hz
      have hy : w*t ∈ ball (0:ℝ) a := by
        rw [mem_ball, dist_zero_right,Real.norm_of_nonneg (by positivity)]
        have hU : w*(δ/(E+w)) ≤ δ := by rw [← mul_div_assoc,div_le_iff₀ he]; nlinarith
        have hk : w*R≤δ := (le_div_iff₀ hr).mp ht
        have hh := mul_le_mul_of_nonneg_left hl hw.le
        unfold δ at *
        nlinarith
      have hk : 1/2<phi (w*t) := hA hy
      unfold leg; rw [(shade u).zero_of_le_dist (by rw [dist_zero_right,Real.norm_of_nonneg hT.le]; exact hz.le),
        sub_zero,one_mul,abs_of_pos hT]
      have ho : t*E ≤ R+δ := calc
        _ ≤ (R+δ/(E+w))*E := mul_le_mul_of_nonneg_right hl hE
        _ ≤ R+δ := by
          rw [add_mul]; refine add_le_add (mul_le_of_le_one_right hr.le h) ?_
          rw [div_mul_eq_mul_div,div_le_iff₀ he]; nlinarith
      calc
        c = Real.exp (-(R+δ))*(1/2) := by unfold c; ring
        _ ≤ _ := mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hk.le (by norm_num) (Real.exp_pos _ |>.le)
    _ ≤ _ := setIntegral_le_integral (leg_int u w E hw hE) (ae_of_all _ fun _ => leg_nn ..)
end YM.Outer
