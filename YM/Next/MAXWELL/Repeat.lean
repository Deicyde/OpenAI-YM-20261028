import Mathlib.Analysis.Calculus.ParametricIntegral
import YM.Next.MAXWELL.Regulator

/-!
# Two contractions with the same enclosed field

Outward flux vanishes even though poles here have very high order. Don't
appeal to extensions of their products. Also utilities on the Welch
collars (only ordinary compact supports).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j l : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma collars_equal {U : Set E4} (hU : IsOpen U) {x : E4} {f g : Field F}
    (H : WaveOn (U \ {x}) f) (K : WaveOn (U \ {x}) g)
    {χ ψ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hψ : ContDiff ℝ ∞ ψ)
    (Hχ : HasCompactSupport χ) (Hψ : HasCompactSupport ψ)
    (hx : χ =ᶠ[𝓝 x] fun _ => 1) (hp : ψ =ᶠ[𝓝 x] fun _ => 1) (hc : tsupport χ ⊆ U) (hd : tsupport ψ ⊆ U)
    {v : Drive} (hv : Killing v) : singleFlux v χ f g = singleFlux v ψ f g := by
  have he : tsupport (χ-ψ) ⊆ U \ {x} := by
    have hw : tsupport (χ-ψ) ⊆ U := (tsupport_sub χ ψ).trans (union_subset hc hd)
    have ht : (χ-ψ) =ᶠ[𝓝 x] 0 := by filter_upwards [hx,hp] with y hy hy'; simp [hy,hy']
    have hq : x ∉ tsupport (χ-ψ) := notMem_tsupport_iff_eventuallyEq.mpr ht
    exact fun y hy => ⟨hw hy, fun h : y=x => hq (h ▸ hy)⟩
  have hy := sourcefree_flux hv (hχ.sub hψ) (Hχ.sub Hψ) he H K (hU.sdiff isClosed_singleton)
  have ht {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
      (hx : χ =ᶠ[𝓝 x] fun _ => 1) (hc : tsupport χ ⊆ U) (a : Axis) :
      Integrable fun y => grad a χ y • current v f g a y := by
    refine shell_cost hχ Hχ ?_ a; intro y hy
    have he : y ∈ U \ {x} := ⟨hc (tsupport_fderiv_subset ℝ hy),fun he : y=x => collar hx (he ▸ hy)⟩
    exact (current_diff hv a (fun i l => H.smooth i l y he) (fun i l => K.smooth i l y he)).continuousAt
  have hf (a : Axis) (y) : grad a (χ-ψ) y = grad a χ y - grad a ψ y := grad_dif
    (hχ.differentiable (by simp) y) (hψ.differentiable (by simp) y) _
  unfold singleFlux exportFlux at hy
  have hl (a : Axis) (y : E4) : grad a (χ-ψ) y • current v f g a y =
      grad a χ y • current v f g a y - grad a ψ y • current v f g a y := by rw [hf,sub_smul]
  change -(∑ a : Axis, ∫ y : E4, grad a (χ-ψ) y • current v f g a y)=0 at hy
  simp_rw [hl] at hy
  simp_rw [integral_sub (ht hχ Hχ hx hc _) (ht hψ Hψ hp hd _), Finset.sum_sub_distrib,
    neg_eq_zero,sub_eq_zero] at hy
  unfold singleFlux exportFlux
  rw [hy]

lemma pulse_hom (p : Probe G j) (a b : Axis) (x y : E4) {t : ℝ} (ht : 0 < t) (hy : y ≠ 0) :
    pulse p x a b (x+t • y) = t⁻¹^(4+j) • pulse p x a b (x+y) := by
  have he : x ≠ x + t • y := by
    have ht' := smul_ne_zero ht.ne' hy; simp [ht']
  have hw : x ≠ x+y := by simp [hy]
  ext1 c
  calc
    _ = K p (omegaLeg c a b) x (x+t • y) := (K_observe p _ _ _ he).symm
    _ = _ := by
      rw [K, show x-(x+t • y) = t • (-y) by rw [smul_neg]; abel,
        (kernel_pole p (omegaLeg c a b)).degree t ht _ (neg_ne_zero.mpr hy),add_zero]
      rw [PiLp.smul_apply,← K_observe p _ _ _ hw,K,show x-(x+y) = -y by abel]

lemma two_flux_zero {x : E4} {χ : E4 → ℝ} (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ)
    (hx : χ =ᶠ[𝓝 x] fun _ => 1) {v : Drive} (h : Killing v)
    (e : ℕ) (he : e ≤ 1) (H : ∀ t : ℝ, 0 < t → ∀ i : Axis, ∀ z : E4, v i (x+t • z)=t^e*v i (x+z))
    (p : Probe G j) (q : Probe G l) : singleFlux v χ (pulse p x) (pulse q x) = 0 := by
  -- Compare to one dilated smooth cut-off. No coincident-point evaluation.
  let f := pulse p x
  let g := pulse q x
  let w := current v f g
  let t := (2:ℝ)
  have ht : 0 < t := by norm_num [t]
  let u := Units.mk0 t ht.ne'
  let s := ((Homeomorph.addRight (-x)).trans (Homeomorph.smul u⁻¹)).trans (Homeomorph.addLeft x)
  have hs (z : E4) : s z = x+t⁻¹ • (z-x) := by simp [s,u,sub_eq_add_neg]; rfl
  let ψ := χ ∘ s
  have hp : ContDiff ℝ ∞ ψ := by
    have hc : ContDiff ℝ ∞ (s : E4 → E4) := by rw [funext hs]; fun_prop
    exact hχ.comp hc
  have hψ : ψ =ᶠ[𝓝 x] fun _ => 1 := by
    have ha := s.continuous.continuousAt (x := x) |>.tendsto
    rw [hs,sub_self,smul_zero,add_zero] at ha
    exact ha hx
  have hc : singleFlux v χ f g = singleFlux v ψ f g := collars_equal isOpen_univ
    (f := f) (g := g) (by rw [← compl_eq_univ_sdiff]; exact pulse_wave p x)
    (by rw [← compl_eq_univ_sdiff]; exact pulse_wave q x) hχ hp Hχ
    (Hχ.comp_homeomorph s) hx hψ (subset_univ _) (subset_univ _) h
  let Dp := t⁻¹^(4+j)
  let Dq := t⁻¹^(4+l)
  let C := t^3*t^e*(Dp*Dq)
  have heq (a : Axis) (z : E4) :
      t^4 * (grad a ψ (x+t • z) • w a (x+t • z)) = C * (grad a χ (x+z) • w a (x+z)) := by
    by_cases h0 : z=0
    · subst z
      rw [smul_zero,add_zero,image_eq_zero_of_notMem_tsupport
        (f := grad a ψ) (x:=x) (fun he => collar hψ (gradient_part ψ a he)),
        image_eq_zero_of_notMem_tsupport (f := grad a χ) (x:=x) (fun he => collar hx (gradient_part χ a he))]; simp
    have hh (a : Axis) : grad a ψ (x+t • z) = t⁻¹ * grad a χ (x+z) := by
      have hj : s (x+t • z) = x+z := by simp [hs,inv_smul_smul₀ ht.ne']
      have hg : HasFDerivAt (s : E4 → E4) (t⁻¹ • ContinuousLinearMap.id ℝ E4) (x+t • z) := by
        rw [funext hs]; exact (((hasFDerivAt_id _).sub_const x).const_smul t⁻¹).const_add x
      unfold grad D ψ; rw [fderiv_comp _ (hχ.differentiable (by simp) _) hg.differentiableAt,hg.fderiv,hj]
      exact map_smul (fderiv ℝ χ _) t⁻¹ _
    have hi (a b : Axis) : cross f g a b (x+t • z) = Dp * Dq * cross f g a b (x+z) := by
      unfold f g cross
      simp only [Dp,Dq,pulse_hom _ _ _ _ z ht h0, real_inner_smul_left, real_inner_smul_right,
        ← mul_add, ← Finset.mul_sum]; ring
    rw [hh a]; simp_rw [w,current,H t ht,hi]
    unfold C; simp only [smul_eq_mul]; simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a _; field_simp
  have hh (a : Axis) : (∫ y : E4, grad a ψ y • w a y) = C * ∫ y : E4, grad a χ y • w a y := by
    rw [dilate_integral (fun y : E4 => grad a ψ y • w a y) x t ht, ← integral_smul]
    rw [show (fun y : E4 => (t^4) • (grad a ψ (x+t • y) • w a (x+t • y))) =
      (fun y => C * (grad a χ (x+y) • w a (x+y))) from funext (heq a), integral_const_mul,
      integral_add_left_eq_self (fun y => grad a χ y • w a y) x]
  let Z := singleFlux v χ f g
  have hz : Z = C*Z := hc.trans (show singleFlux v ψ f g = C*Z by
    change -(∑ a : Axis, ∫ y : E4, grad a ψ y • w a y) = _
    simp_rw [hh,← Finset.mul_sum]; rw [← mul_neg]; rfl)
  have hlt : C < 1 := by
    have hj : Dp ≤ t⁻¹^4 := pow_le_pow_of_le_one (by positivity) (by norm_num [t]) (by omega)
    have hl : Dq ≤ t⁻¹^4 := pow_le_pow_of_le_one (by positivity) (by norm_num [t]) (by omega)
    have hg : t^e ≤ t := by simpa only [pow_one] using (pow_le_pow_right₀ (by norm_num [t] : 1 ≤ t) he)
    unfold C; calc
      _ ≤ t^3*t*(t⁻¹^4 * t⁻¹^4) := by gcongr
      _ < 1 := by norm_num [t]
  change Z=0
  exact (mul_eq_zero.mp (show (1-C)*Z=0 from by linarith only [hz])).resolve_left (by linarith only [hlt])

end YM.Maxwell.Free
