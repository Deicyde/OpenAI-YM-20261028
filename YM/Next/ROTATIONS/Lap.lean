import YM.Next.ROTATIONS.Profile
/-!
# Temporal response with parity. Conventions from E (normalized position pairing in
Slices). Keep positive spectrum and actual zero mode. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe
open scoped Topology BigOperators NNReal ENNReal ContDiff InnerProductSpace

theorem Lap_cont (b : ℂ) (hb : ‖b‖=1) (f : Form) : ContinuousOn (Lap b f) (Ici 0) := by
  apply continuousOn_iff_continuous_restrict.mpr
  apply continuous_of_dominated (F:=fun (E : Ici (0:ℝ)) t => damped b f E t)
    (bound := fun t => ‖hat f t‖) (fun E => (damped_fiber _ f E.property).1) ?_ (hat f).integrable.norm
  · exact ae_of_all _ fun t => by unfold damped;fun_prop
  intro E; filter_upwards with t
  rw [damped_n b hb]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (abs_nonneg _)) E.property)

private lemma half (b) (f : Profile) (E : ℝ) (hE : 0<E) : Lap b (stamp f) E = ∫ p : ℝ,
    (((E:ℂ)+↑p*I)⁻¹ + b*((E:ℂ)-↑p*I)⁻¹)*(f p:ℂ) := by
  have hz : ∫ t : ℝ in Ioi 0,damped b (stamp f) E (-t) = ∫ t : ℝ in Iic 0,damped b (stamp f) E t := by
    simp
  let μ := (volume : Measure ℝ).restrict (Ioi 0)
  let u (a : ℝ) p := -(E:ℂ)+(a:ℝ)*(p:ℝ)*I
  have hU (a p : ℝ) : (u a p).re<0 := by simp [u,hE]
  have hi (a b : ℝ) : (∫ t,Complex.exp (u a b*(t:ℂ)) ∂μ) = (-u a b)⁻¹ := by
    rw [show μ=volume.restrict _ from rfl, integral_exp_mul_complex_Ioi (hU a b)]; simp [div_eq_mul_inv]
  let L (a t p : ℝ) := Complex.exp (u a p * ↑t)*(f p : ℂ)
  have hI a : Integrable (uncurry (L a)) (μ.prod volume) := by
    refine ((integrableOn_exp_mul_Ioi (by linarith : -E<0) 0).mul_prod f.integrable.norm).mono' ?_ ?_
    · unfold uncurry L u; fun_prop
    filter_upwards with x; rcases x with ⟨t,p⟩
    change ‖Complex.exp _ * _‖ ≤ _; simp [Complex.norm_exp, u]
  have hL a : (∫ t, ∫ p, L a t p ∂(volume : Measure ℝ) ∂μ) = ∫ p : ℝ, (-u a p)⁻¹ * (f p:ℂ) := by
    rw [integral_integral_swap (hI _)]; unfold L; simp_rw [integral_mul_const,hi]
  have hh a : Integrable (fun p : ℝ => (-u a p)⁻¹ * (f p:ℂ)) := by
    simp_rw [← hi,← integral_mul_const]; exact (hI a).integral_prod_right
  unfold Lap
  rw [← integral_add_compl (s:=Ioi 0) measurableSet_Ioi (damped_fiber b (stamp f) hE.le), compl_Ioi, ← hz]
  have ht (t : ℝ) (hr : 0<t) : damped b (stamp f) E t = ∫ p,L (-1) t p := by
    unfold damped; rw [side, if_neg (by linarith),abs_of_pos hr,hat_eq,← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only [L]; rw [stamp_at,one_mul,← mul_assoc, plane, ofReal_exp,← Complex.exp_add]
    congr 2; unfold u; simp; ring
  have hx (t : ℝ) (hr : 0<t) : damped b (stamp f) E (-t)= b * ∫ p,L 1 t p := by
    unfold damped; rw [side, if_pos (by linarith),abs_neg,abs_of_pos hr,hat_eq,mul_assoc]
    congr 1; rw [← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun p => ?_)
    dsimp only [L]; rw [stamp_at, ← mul_assoc, plane, ofReal_exp, ← Complex.exp_add]; congr 2
    unfold u; simp; ring
  change integral μ _ + integral μ _ = _
  rw [integral_congr_ae (show _ from ae_restrict_of_forall_mem measurableSet_Ioi ht),
    integral_congr_ae (show _ from ae_restrict_of_forall_mem measurableSet_Ioi hx), integral_const_mul,hL,hL,
    ← integral_const_mul, ← integral_add (hh _) ((hh _).const_mul _)]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only; rw [show -u (-1) p=(E:ℂ)+(p:ℂ)*I by simp [u,add_comm], show -u 1 p=(E:ℂ)-(p:ℂ)*I by simp [u]; ring, add_mul,mul_assoc]

private lemma combine (x y : ℝ) (hx : 0<x) : let a := (x:ℂ)+(y:ℂ)*I; let b := (x:ℂ)-(y:ℂ)*I
    a⁻¹+b⁻¹=(2*x/(x^2+y^2):ℝ) ∧ a⁻¹-b⁻¹= (-2*I)*(y/(x^2+y^2) : ℝ) := by
  intro a b
  have hD : x^2+y^2 ≠ 0 := by positivity
  have he : ((x^2+y^2:ℝ):ℂ)=a*b := by unfold a b;push_cast; ring_nf; simp [I_sq]
  have hn : a*b≠0 := he ▸ (ofReal_ne_zero.mpr hD)
  have ha := (mul_ne_zero_iff.mp hn).1
  have hb := (mul_ne_zero_iff.mp hn).2
  rw [ofReal_div,ofReal_div,he,ofReal_mul]
  constructor
  · field_simp
    dsimp only [a,b]; push_cast; ring
  · field_simp; unfold a b; ring

lemma evenLap (f : Profile) (E : ℝ) (hE : 0<E) : Lap 1 (stamp f) E=
    Complex.ofReal (∫ p : ℝ,(f p * (2*E/(E^2+p^2)):ℝ)) := by
  rw [half _ _ _ hE, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [one_mul]; rw [(combine E p hE).1,ofReal_mul (f p),mul_comm]

lemma oddLap (f : Profile) (E : ℝ) (hE : 0<E) : Lap (-1) (stamp f) E=
    (-2*I)* ↑(∫ p : ℝ,f p * (p/(E^2+p^2))) := by
  rw [half _ _ _ hE, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [neg_mul, one_mul,← sub_eq_add_neg]
  rw [(combine E p hE).2,ofReal_mul (f p)]; ring
lemma zeroLap (f : Profile) : Lap 1 (stamp f) 0= ↑(pref ℝ * f 0) := by
  have he := positiveFourier (stamp f) 0
  simp only [plane_zero,one_mul,stamp_at,Complex.real_smul] at he
  simpa [Lap,damped,side] using he

lemma Lap_add (b) (f g : Form) (E : ℝ) (hE : 0≤E) : Lap b (f+g) E= Lap b f E+Lap b g E := by
  unfold Lap
  rw [← integral_add (damped_fiber b f hE) (damped_fiber b g hE)]
  congr 1; ext x; simp [damped,mul_add]
lemma Lap_sub (b) (f g : Form) (E : ℝ) (hE : 0≤E) : Lap b (f-g) E=Lap b f E-Lap b g E := by
  refine eq_sub_of_add_eq <| ?_
  rw [← Lap_add b _ _ _ hE,sub_add_cancel]
end YM.Outer
