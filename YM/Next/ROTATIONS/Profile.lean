import YM.Next.ROTATIONS.Flat
import YM.Next.ROTATIONS.Slices
/-! # Fixed rescaled profiles. -/
noncomputable section
namespace YM.Outer
open Function Filter Set MeasureTheory Measure Complex Boundary Probe
open scoped Topology ContDiff BigOperators NNReal ENNReal InnerProductSpace
abbrev Profile := SchwartzMap ℝ ℝ

def stamp : Profile →L[ℝ] Form := SchwartzMap.postcompCLM ofRealCLM
lemma stamp_at (f : Profile) (t) : stamp f t = (f t:ℂ) := rfl
/-- scale in frequency (L1 normalization); 0 width never used. -/
def width (w : ℝ) : Profile →L[ℝ] Profile := if h : w=0 then 0 else w⁻¹ • SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
  (ContinuousLinearEquiv.smulLeft (Units.mk0 w⁻¹ (inv_ne_zero h)))
lemma width_at (w : ℝ) (f : Profile) (p : ℝ) : width w f p = w⁻¹*f (p/w) := by
  unfold width; split_ifs with h
  · simp [h]
  change w⁻¹*f (w⁻¹*p)=_
  rw [div_eq_mul_inv, mul_comm p]

lemma pat (w : ℝ) (h : 0<w) (f : Profile) (g : ℝ → ℝ) :
    (∫ x,width w f x * g x) = ∫ x, f x*g (w*x) := by
  have hh := Measure.integral_comp_mul_left (fun x : ℝ => width w f x * g x) w
  simp_rw [width_at] at *
  simp only [abs_of_pos (inv_pos.mpr h),mul_div_cancel_left₀ _ h.ne',mul_assoc, integral_const_mul] at hh
  exact mul_left_cancel₀ (inv_pos.mpr h).ne' (by simpa only [smul_eq_mul,mul_assoc,integral_const_mul] using hh.symm)

def pump (j : ℕ) : Profile →L[ℝ] Profile := SchwartzMap.smulLeftCLM ℝ (fun x : ℝ => x^j)
lemma pump_at (j : ℕ) (f : Profile) (p : ℝ) : pump j f p=p^j*f p := by
  refine SchwartzMap.smulLeftCLM_apply_apply ?_ f p
  fun_prop
lemma pump_width (j : ℕ) (w : ℝ) (f : Profile) : pump j (width w f)=(w^j:ℝ) • width w (pump j f) := by
  ext x
  simp only [pump_at,width_at,_root_.smul_apply,smul_eq_mul]
  by_cases h : w=0
  · simp [h]
  rw [div_pow]; field_simp
lemma pump_pump (j k : ℕ) (f : Profile) : pump j (pump k f)=pump (j+k) f := by
  ext x; rw [pump_at,pump_at,pump_at,pow_add,mul_assoc]

def tally (j : ℕ) : Profile →L[ℝ] ℝ := (SchwartzMap.integralCLM ℝ volume).comp (pump j)
lemma counts (j : ℕ) (f : Profile) : tally j f=∫ p : ℝ,p^j*f p := by
  change (∫ p : ℝ, pump j f p)=_
  simp_rw [pump_at]
lemma tally_width (j : ℕ) (w : ℝ) (hp : 0<w) (f : Profile) : tally j (width w f)=w^j*tally j f := by
  simp_rw [counts]; rw [integral_congr_ae (ae_of_all _ fun _ => mul_comm _ (width w f _)),pat w hp f (fun p => p^j)]
  rw [← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun p => ?_); simp only [mul_pow]; ring

def Centred (k : ℕ) (f : Profile) := ∀ j, j<k → tally j f=0

private lemma orbit (x t : ℝ) : HasDerivAt (fun t : ℝ => plane x (-t)) (-I*(x:ℂ)*plane x (-t)) t := by
  have hx := ((((hasDerivAt_id' t).ofReal_comp).const_mul (↑x:ℂ)).neg.mul_const I).cexp
  convert hx using 1
  · ext1 p; simp [plane,mul_comm]
  simp [plane]; ring_nf
lemma slope (f : Profile) (x : ℝ) : HasDerivAt (hat (stamp f)) (-I * hat (stamp (pump 1 f)) x) x := by
  let z (t p : ℝ) := plane p (-t)*(f p:ℂ)
  let v (t p : ℝ) := -I * (plane p (-t) * (pump 1 f p:ℂ))
  have hz (t p : ℝ) : HasDerivAt (fun t => z t p) (v t p) t := by
    have he : v t p = (-I*(p:ℂ)*plane p (-t))*(f p:ℂ) := by unfold v; rw [pump_at,pow_one,ofReal_mul]; ring
    rw [he]; exact (orbit p t).mul_const (f p:ℂ)
  have hw : Integrable (z x) := by
    apply f.integrable.ofReal.bdd_mul (c:=1) ?_ (ae_of_all _ fun p => le_of_eq (plane_norm p _))
    unfold plane; fun_prop
  have ht := hasDerivAt_integral_of_dominated_loc_of_deriv_le (F:=z) (F':=v) (μ:=volume) (x₀:=x)
    (bound:=fun p => ‖pump 1 f p‖) (s:=univ) univ_mem (Eventually.of_forall fun _ => by unfold z plane; fun_prop) hw (by unfold v plane; fun_prop) (ae_of_all _ fun p x _ => by
      simp only [v,norm_mul,norm_neg,norm_I,plane_norm,Complex.norm_real,one_mul,le_rfl]) (pump 1 f).integrable.norm
    (ae_of_all _ fun p t _ => hz t p)
  have he : (∫ a,v x a)= -I * hat (stamp (pump 1 f)) x := by unfold v;rw [integral_const_mul,hat_eq];rfl
  rw [he] at ht
  rw [show ⇑(hat (stamp f))=(fun x => ∫ p,z x p) by funext p; exact hat_eq ..]
  exact ht.2

lemma moment_jet (f : Profile) (k : ℕ) (x : ℝ) : iteratedDeriv k (hat (stamp f)) x=(-I)^k*hat (stamp (pump k f)) x := by
  induction k generalizing x with
  | zero =>
    have he : pump 0 f=f := by ext t; simp [pump_at]
    simp [he]
  | succ k ih =>
    rw [iteratedDeriv_succ, funext ih]
    rw [show deriv _ x=_ from ((slope (pump k f) x).const_mul ((-I)^k)).deriv, pump_pump,pow_succ,add_comm 1]
    ring

lemma jet_at_origin (f : Profile) (k) : iteratedDeriv k (hat (stamp f)) 0=(-I)^k*(tally k f:ℂ) := by
  rw [moment_jet,hat_eq,neg_zero]
  simp_rw [plane_zero, one_mul]
  simp_rw [stamp_at,pump_at]
  rw [counts,integral_complex_ofReal]

lemma centred_hollow (f : Profile) (k) (h : Centred k f) : Hollow (stamp f) k := by
  have hi (j : ℕ) (hh : j<k) : iteratedFDeriv ℝ j (hat (stamp f)) 0=0 := norm_eq_zero.mp <| by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,jet_at_origin,h _ hh]; simp
  obtain ⟨C,hC,h⟩ := earnings (F:=ℂ) _ ((hat (stamp f)).smooth ⊤) 0 k (fun _ _ hz => hi _ (by omega)) 1
  exact ⟨C,hC, fun t _ ht => by simpa [Real.norm_eq_abs] using h t ht⟩
end YM.Outer
