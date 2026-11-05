import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! Concrete radial/Taylor subtraction utilities on the full smooth test class. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact
open Set Function Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff InnerProductSpace BigOperators Classical

variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E]

/-- Common C∞ radial profile. -/
def χ : ContDiffBump (0:ℝ):=⟨1,4,zero_lt_one,by norm_num⟩
def cutoff (s:ℝ) (x:E) : ℝ:=χ (‖x‖^2/s^2)
omit [InnerProductSpace ℝ E] in
lemma cutoff_eq_one {s:ℝ}(hs:0<s) {x:E}(hx:‖x‖≤s):cutoff s x=1:=by
     apply χ.one_of_mem_closedBall
     have he:0 ≤ ‖x‖^2/s^2:=by positivity
     rw [Metric.mem_closedBall,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg he]
     exact (div_le_one (sq_pos_of_pos hs)).2 ((sq_le_sq₀ (norm_nonneg x) hs.le).2 hx)
omit [InnerProductSpace ℝ E] in
lemma cutoff_eq_zero {s:ℝ}(hs:0<s) {x:E}(hx:2*s≤‖x‖):cutoff s x=0:=by
     apply χ.zero_of_le_dist
     rw [dist_zero_right]; refine le_trans ?_ (Real.le_norm_self _)
     exact ((le_div_iff₀ (sq_pos_of_pos hs)).2 (by dsimp [χ]; nlinarith [(norm_nonneg x)]))
omit [InnerProductSpace ℝ E] in
lemma cutoff_mem (s:ℝ)(x:E):0≤cutoff s x ∧ cutoff s x≤1:= ⟨χ.nonneg,χ.le_one⟩
lemma cutoff_smooth (s:ℝ):ContDiff ℝ ∞ (cutoff (E:=E) s):=χ.contDiff |>.comp ((contDiff_id.norm_sq (𝕜:=ℝ)).div_const _)

def coeff (i:ℕ)(f : E→ℂ)(y:E) := (↑(i.factorial):ℝ)⁻¹ • iteratedFDeriv ℝ i f 0 (fun _=>y)
def polyJet (m:ℕ)(f : E→ℂ)(y:E) :=∑ i∈ Finset.range (m+1),coeff i f y
def diff (s:ℝ)(m:Option ℕ)(f:E→ℂ):E→ℂ:=match m with
 | none=> f
 | some m=> fun y=>f y-cutoff s y • polyJet m f y

lemma coeff_contDiff (f:E→ℂ)(i:ℕ):ContDiff ℝ ∞ (coeff i f):=by
    refine (iterate_after _).const_smul _
 where
  iterate_after (i:ℕ):ContDiff ℝ ∞ (fun x=>iteratedFDeriv ℝ i f (0:E) fun _=>x):=by
     exact (iteratedFDeriv ℝ i f 0).contDiff.comp (contDiff_pi.mpr fun _=>contDiff_id)
lemma polyJet_contDiff (m:ℕ)(f:E→ℂ):ContDiff ℝ ∞ (polyJet m f):=by exact ContDiff.sum (fun i _=>coeff_contDiff f i)
lemma diff_contDiff {f:E→ℂ}(hf:ContDiff ℝ ∞ f) (s:ℝ) : ∀ m,ContDiff ℝ ∞ (diff s m f)
 | none=>hf
 | some m=>hf.sub ((cutoff_smooth s).smul (polyJet_contDiff m f))

lemma poly_integral {f:E→ℂ} (hs:ContDiff ℝ ∞ f) (m:ℕ) (y:E):
  f y= polyJet m f y + (↑m.factorial:ℝ)⁻¹ • ∫ t:ℝ in 0..1,(1-t)^m • iteratedFDeriv ℝ (m+1) f (t • y) (fun _=>y):=by
  simpa only [zero_add, coeff,polyJet] using (map_add_eq_sum_add_integral_iteratedFDeriv (x:=(0:E)) (n:=m) (y:=y) fun t _=> hs.contDiffAt.of_le (by norm_cast;exact le_top))

def JetBounds (m:ℕ) (f:E→ℂ) (A:ℝ) : Prop:= 0 ≤ A ∧ ∀ y:E,∀ i:ℕ,i≤m→ ‖iteratedFDeriv ℝ i f y‖ ≤ A
theorem JetBounds.value {m:ℕ}{f:E→ℂ}{A:ℝ}(h:JetBounds m f A)(x:E):‖f x‖≤A:=by simpa only [norm_iteratedFDeriv_zero] using h.2 x 0 (Nat.zero_le _)
theorem JetBounds.weaker {m k:ℕ}{f:E→ℂ}{A:ℝ}(h:JetBounds k f A)(hm:m ≤ k):JetBounds m f A:=⟨h.1,fun y i hi=> h.2 y i (hi.trans hm)⟩
theorem fact_mul_bound {x:ℂ}{n:ℕ}:‖(↑n.factorial:ℝ)⁻¹ • x‖≤‖x‖:=by
   rw [norm_smul]; refine mul_le_of_le_one_left (norm_nonneg _) ?_
   rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.factorial_pos n|>.ne')))
lemma JetBounds.peak {m:ℕ}{f:E→ℂ}{B}(h:JetBounds m f B)(z y:E)(i:ℕ)(hi:i≤m):‖(iteratedFDeriv ℝ i f z) (fun _=>y)‖ ≤ B*‖y‖^i:= by
   
   refine ((iteratedFDeriv ℝ i f z).le_opNorm (fun _=>y)).trans ?_; simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]; exact (mul_le_mul_of_nonneg_right (h.2 z i hi) (by positivity))
theorem poly_bound {f:E→ℂ}{A:ℝ}{m:ℕ} (hs:ContDiff ℝ ∞ f)(ha:JetBounds (m+1) f A) (y:E):
    ‖f y - polyJet m f y‖ ≤ A*‖y‖^(m+1):=by
    nth_rw 1 [poly_integral hs m y]; rw [add_sub_cancel_left]; apply fact_mul_bound.trans
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C:=A*‖y‖^(m+1)) ?_).trans (by norm_num)
    intro t ht
    have ht : t∈Set.Ioc 0 1:=by rwa [Set.uIoc_of_le zero_le_one] at ht
    apply le_trans ?_ (ha.peak (t•y) y (m+1) le_rfl)
    rw [norm_smul]; refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [norm_pow,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2])]; exact pow_le_one₀ (by linarith [ht.2]) (by linarith [ht.1])

-- test with normalized Jacobian and arbitrary shrinking length r.
def scaled [FiniteDimensional ℝ E](r:ℝ)(f:E→ℂ)(x:E):ℂ := (r^(Module.finrank ℝ E))⁻¹ • f (r⁻¹ • x)
lemma scaled_jet [FiniteDimensional ℝ E]{f:E→ℂ}(hs:ContDiff ℝ ∞ f)(r:ℝ)(m:ℕ)(y:E):
   polyJet m (scaled r f) y=(r^(Module.finrank ℝ E))⁻¹ • polyJet m f (r⁻¹ • y):=by
   have he (i:ℕ):coeff i (scaled r f) y=(r^(Module.finrank ℝ E))⁻¹ • coeff i f (r⁻¹ • y):=by
      let L : E →L[ℝ] E := (r⁻¹:ℝ) • .id ℝ E
      let q := r^(Module.finrank ℝ E); unfold coeff
      change (↑i.factorial:ℝ)⁻¹ • (iteratedFDeriv ℝ i (q⁻¹ • (f ∘ (L:E→E))) 0 (fun _=>y))=_
      rw [iteratedFDeriv_const_smul_apply, L.iteratedFDeriv_comp_right hs]
      · change (↑i.factorial:ℝ)⁻¹ • (q⁻¹ • iteratedFDeriv ℝ i f (L 0) (fun _=>L y))=_
        rw [map_zero]; exact smul_comm ..
      · norm_cast; exact le_top
      · exact (hs.comp L.contDiff).contDiffAt.of_le (by norm_cast; exact le_top)
   unfold polyJet; simp only [he,Finset.smul_sum]

lemma diff_scaled [FiniteDimensional ℝ E]{f:E→ℂ}(hs:ContDiff ℝ ∞ f)
    (r s:ℝ)(hr:0<r) (hR:r≤s){A:ℝ}{m:ℕ}(ha:JetBounds (m+1) f A)(y:E):
   ‖diff s (some m) (scaled r f) y‖ ≤ (m+4:ℝ) * A * (r^(Module.finrank ℝ E))⁻¹ * min ((‖y‖/r)^(m+1)) ((‖y‖/r)^m):=by
   have hy:0≤ ‖y‖/r:=by positivity
   have hp:= (sq_pos_of_pos hr); let g:= ‖y‖/r
   have ht:‖r⁻¹ • y‖=g:=by dsimp [g]; simp [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le), div_eq_inv_mul]
   have he: ‖diff s (some m) (scaled r f) y‖=(r^(Module.finrank ℝ E))⁻¹ * ‖f (r⁻¹ • y) - cutoff s y • polyJet m f (r⁻¹ • y)‖ :=by
       dsimp only [diff]; rw [scaled_jet hs r]; unfold scaled; rw [smul_comm (cutoff s y) ((r^(Module.finrank ℝ E))⁻¹),← smul_sub,norm_smul,Real.norm_of_nonneg (by positivity)] -- check
   rw [he]
   by_cases hg : ‖y‖ ≤ r
   · rw [cutoff_eq_one (hr.trans_le hR) (hg.trans hR), one_smul,min_eq_left (pow_le_pow_of_le_one hy ((div_le_one hr).2 hg) (Nat.le_succ _))]
     apply (mul_le_mul_of_nonneg_left (by simpa only [ht] using (poly_bound hs ha (r⁻¹•y))) (by positivity : 0≤(r^(Module.finrank ℝ E))⁻¹)).trans
     have hm:= ha.1; have hq:= show 0 ≤ (r^Module.finrank ℝ E)⁻¹ * (A * (‖y‖/r)^(m+1)) by positivity
     dsimp [g]
     simp only [pow_succ] at hq ⊢; nlinarith only [mul_nonneg hq (Nat.cast_nonneg (α:=ℝ) m), hq]
   have hg' := (one_le_div₀ hr).2 (le_of_not_ge hg)
   have hh (i:ℕ)(hi:i<m+1):‖coeff i f (r⁻¹ • y)‖ ≤ A*g^m := fact_mul_bound.trans (by
      rw [← ht]; exact (ha.peak 0 (r⁻¹ • y) _ (by omega)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by rwa [ht]) (by omega : i≤m)) ha.1))
   have hv: ‖polyJet m f (r⁻¹ • y)‖ ≤ (m+1:ℝ) * (A*g^m) := (norm_sum_le ..).trans (by
      refine (Finset.sum_le_sum (fun i hi=>hh i (Finset.mem_range.mp hi))).trans ?_
      simp)
   rw [min_eq_right (pow_le_pow_right₀ hg' (Nat.le_succ _))]
   refine (mul_le_mul_of_nonneg_left (a:=(r^Module.finrank ℝ E)⁻¹) (c:=A+‖polyJet m f (r⁻¹ • y)‖) ?_ (by positivity)).trans ?_
   · apply (norm_sub_le ..).trans (add_le_add (ha.value _) ?_)
     rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg (cutoff_mem s y).1]; exact (cutoff_mem s y).2)
   have hp:g=‖y‖/r:=rfl; rw [hp] at *; exact (mul_le_mul_of_nonneg_left (by rw [add_mul]; rw [add_mul]; nlinarith only [hv,mul_nonneg (sub_nonneg.mpr (one_le_pow₀ hg' (n:=m))) ha.1,ha.1] : A+‖polyJet m f _‖ ≤ (m+2:ℝ)* A*(‖y‖/r)^m) (by positivity : 0≤(r^(Module.finrank ℝ E))⁻¹)).trans (by nlinarith only [show 0 ≤ (‖y‖/r)^m * A* (r^(Module.finrank ℝ E))⁻¹ by have h := ha.1; positivity] )

lemma diff_bound {s:ℝ}{f:E→ℂ}(hs:0<s)(hf:ContDiff ℝ ∞ f)(m:ℕ){A:ℝ}(h:JetBounds (m+1) f A)(y:E):
    ‖diff s (some m) f y‖ ≤ ((m+2:ℝ) * (1+s⁻¹)^(m+1) * A) * ‖y‖^(m+1):=by
      have hp:=h.1; have ht:1 ≤ (1 + s⁻¹):= by have hg := inv_nonneg.mpr hs.le; linarith
      let T:=(1+s⁻¹)^(m+1); have hT:1 ≤ T:=one_le_pow₀ ht
      by_cases hy:‖y‖ ≤ s
      · rw [diff]; dsimp only; rw [cutoff_eq_one hs hy,one_smul]
        have he:A≤ (m+2:ℝ)*T*A:=(le_mul_of_one_le_left hp (by have hv:=Nat.cast_nonneg (α:=ℝ) m; nlinarith only [mul_nonneg (sub_nonneg.mpr hT) hv,hv,hT] : 1≤(m+2:ℝ)*T))
        exact (poly_bound hf h y).trans (mul_le_mul_of_nonneg_right he (by positivity))
      have hy':1 ≤ (1+s⁻¹)*‖y‖:=by
          suffices 1 ≤ ‖y‖ / s by rw [add_mul,one_mul,← div_eq_inv_mul]; linarith only [this,norm_nonneg y]
          exact (one_le_div₀ hs).2 (le_of_not_ge hy)
      have hu (i:ℕ)(hi:i≤m+1):‖y‖^i ≤ T*‖y‖^(m+1):=by
        by_cases hx:‖y‖≤1
        · unfold T; rw [← mul_pow]; exact (pow_le_one₀ (norm_nonneg y) hx).trans (one_le_pow₀ hy')
        exact (pow_le_pow_right₀ (le_of_not_ge hx) hi).trans (le_mul_of_one_le_left (by positivity) hT)
      have hg: ‖polyJet m f y‖ ≤ (m+1:ℝ)*(A*(T*‖y‖^(m+1))) := (norm_sum_le ..).trans (le_trans (Finset.sum_le_sum (fun i hi=> (@fact_mul_bound _ i).trans ((h.peak 0 y i (Nat.le_of_lt (Finset.mem_range.mp hi))).trans (mul_le_mul_of_nonneg_left (hu i (Nat.le_of_lt (Finset.mem_range.mp hi))) h.1)))) (by simp))
      have hl: ‖polyJet m f y‖ ≥ ‖cutoff s y • polyJet m f y‖:=by rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_of_nonneg (cutoff_mem s y).1]; exact (cutoff_mem s y).2)
      refine (norm_sub_le ..).trans ((add_le_add ((h.value y).trans (le_trans ?_ (mul_le_mul_of_nonneg_left (hu 0 (by omega)) h.1))) hl).trans ?_)
      · simp
      change A * _ + _ ≤ (m+2:ℝ)*T*A*_; linarith only [hg]
end YM.MultipleContact
