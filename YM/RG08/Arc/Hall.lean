import YM.RG08.Dew.Cedar
import YM.PertExtension.Aspiration
/-! # Local asymmetric windows, finite Laplace coefficients
No history uniformity. Auxiliary proof for Ward: compare arbitrarily oddly shaped
windows converging to neighborhoods of unit in alternative slices, allowing active
Haar chart shifted by a t-dependent analytic mean. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial
open scoped BigOperators Topology Real ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][MeasurableSpace E][BorelSpace E]

private lemma interior_cap {K f : E→ℝ}(h : ContinuousAt K 0) (hp : Stationary f) (H : ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u) :
    ∃ δ>0, ∃ B c : ℝ,0≤B ∧ 0<c ∧ ∀ r:ℝ, r≤δ → ∀ t>0, ∀ u ∈ disc t r, ‖YM.PertExtension.Series.Radial.projection K f t u‖≤ B*bill (E:=E) 0 c u := by
  obtain ⟨c,hc,H⟩:=H; let z:=c/2; have hz : 0<z:=half_pos hc
  obtain ⟨ε,D,hε,hD,hd⟩:=hp.dominated hz
  let C:=‖K 0‖+1
  obtain ⟨δ,hδ,he⟩:=(Metric.mem_nhds_iff (s:={x|‖K x‖ < C})).mp (h.norm.eventually_lt continuousAt_const (by dsimp [C]; linarith))
  refine ⟨min δ ε,lt_min hδ hε,C,z,by dsimp [C]; positivity,hz,fun r hr t ht u hu=>?_⟩
  have ha : ‖K (t•u)‖<C:= he ((ball_subset_ball (hr.trans (min_le_left ..))) hu)
  have hM : ‖higher f t u‖≤z*‖u‖^2 := (hd u t ht (((disc_mem ht.le r u).mp hu).le.trans (hr.trans (min_le_right ..)))).2
  have hy : Real.exp (higher f t u)*kernel f u≤bill 0 z u := by
    rw [show bill 0 z u= Real.exp (-z*‖u‖^2) from by simp [bill]]
    exact le_trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ((le_abs_self _).trans hM)) kernel_pos.le) (kernel_bound (f:=f) (r:=z) (by unfold z; grw [show c/2+c/2=c by ring,H]))
  unfold YM.PertExtension.Series.Radial.projection insertion; rw [mul_assoc, norm_mul, Real.norm_eq_abs (Real.exp _ * kernel ..), abs_of_nonneg (mul_nonneg (Real.exp_pos _).le kernel_pos.le)]
  exact mul_le_mul ha.le hy (mul_nonneg (Real.exp_pos _).le kernel_pos.le) (by dsimp [C]; positivity)

private lemma ash (μ : Measure E) [μ.HasTemperateGrowth] {K f : E→ℝ}{u : ℕ} {c B ε t : ℝ} {S : Set E}
    (hS : MeasurableSet S) (hb : ∀ x∈S, ‖YM.PertExtension.Series.Radial.projection K f t x‖≤ B*bill 0 c x)
    (hX : S ⊆ (disc t ε)ᶜ) (ht : 0≤t) (hc : 0<c) (hp : 0≤B) (hz : 0<ε) :
    ‖∫ x in S, YM.PertExtension.Series.Radial.projection K f t x ∂μ‖ ≤ (∫ x:E,bill u c x ∂μ)*(B*(ε⁻¹)^u)*t^u := by
  let D:=B*ε⁻¹^u*t^u; have hD:0≤D:=by unfold D; positivity
  let F x:=D*bill (E:=E) u c x
  have hi : Integrable F μ := (bill_integrable μ u hc).const_mul _
  refine (norm_integral_le_of_norm_le (hi.mono_measure (Measure.restrict_le_self)) ?_).trans ((setIntegral_le_integral hi (Eventually.of_forall fun x=>mul_nonneg hD (bill_nonneg ..))).trans_eq ?_)
  · filter_upwards [ae_restrict_mem hS] with x hx
    have he : ε≤ t*‖x‖ := by_contra fun e=> hX hx ((disc_mem ht _ x).2 (lt_of_not_ge e))
    apply (hb x hx).trans
    have hL : 1 ≤ t*(1+‖x‖)*ε⁻¹ := (le_mul_inv_iff₀ hz).mpr (by linarith)
    refine (le_mul_of_one_le_right (mul_nonneg hp (bill_nonneg ..)) (one_le_pow₀ hL (n:=u))).trans_eq ?_
    unfold bill F D; change _= B*ε⁻¹^u*t^u*((1+‖x‖)^u*_); simp only [pow_zero, one_mul, mul_pow]; ring
  unfold F; rw [integral_const_mul]; unfold D; ring

-- control uniformly over all asymmetric sets at a fixed step/order/window, positive pulse direction
lemma localized (μ : Measure E) [μ.HasTemperateGrowth] {K f : E→ℝ} (h : ContDiffAt ℝ ∞ K 0)
    (hK : Measurable K) (hf : Measurable f) (hp : Stationary f)
    (H : ∃ c>0,∀ u:E,c*‖u‖^2≤jet f 2 u) (n : ℕ) :
    ∃ δ>0,∀ r:ℝ,0<r → r≤δ → ∀ A:ℝ→Set E, (∀ᶠ t in 𝓝[>] (0:ℝ), MeasurableSet (A t) ∧ A t⊆disc t r) →
      (∃ ε>0,∀ᶠ t in 𝓝[>] (0:ℝ), disc t ε⊆A t) →
      Bill (n+1) ((fun t=> ∫ x in A t, YM.PertExtension.Series.Radial.projection K f t x ∂μ) - peval (moment μ K f) n) := by
  obtain ⟨δ,hδ,ht⟩:= hp.rescale_estimate μ h hK hf H n
  obtain ⟨κ,hκ,B,c,hB,hc,H⟩:= interior_cap h.continuousAt hp H
  refine ⟨min (δ/2) κ,lt_min (by positivity) hκ,fun r hr hu A Hv ⟨ε,hε,hE⟩=>?_⟩
  obtain ⟨C,hQ⟩:=ht r ⟨hr,lt_of_le_of_lt (hu.trans (min_le_left ..)) (half_lt_self hδ)⟩
  let L:=(∫ x:E,bill (n+1) c x ∂μ)*(B*ε⁻¹^(n+1))
  refine ⟨|C|+|L|,by positivity,?_⟩
  filter_upwards [Hv,hE,hQ,eventually_pos] with t ⟨he,hV⟩ hU hW hx
  let F := YM.PertExtension.Series.Radial.projection K f t; let s := A t; let D:=disc (E:=E) t r
  have hL x (hp : x∈D) : ‖F x‖≤ B*bill 0 c x := H r (hu.trans (min_le_right ..)) t hx _ hp
  have hi : IntegrableOn F D μ := ((bill_integrable μ 0 hc).const_mul B).integrableOn.mono' ((projection_meas hK hf t).aestronglyMeasurable) ((ae_restrict_iff' (disc_meas ..)).2 (Eventually.of_forall hL)) -- elaboration
  let P := peval (moment μ K f) n t
  change ‖(∫ x in s,F x ∂μ)- P‖≤_
  rw [show (∫ x in s,F x ∂μ)-P=((∫ x in D,F x ∂μ)-P)-(∫ x in D\s,F x ∂μ) by rw [setIntegral_sdiff he hi hV]; abel]
  refine (norm_sub_le ..).trans ((add_le_add (show ‖(∫ x in D,F x ∂μ)-P‖ ≤ _ from hW)
      (ash μ (u:=n+1) ((disc_meas ..).diff he) (fun i (hx : i∈D\s)=> hL i hx.1) (fun i hi=> fun hy=> hi.2 (hU hy)) hx.le hc hB hε)).trans ?_)
  change C*_+L*t^(n+1)≤_
  rw [add_mul]; exact add_le_add (mul_le_mul_of_nonneg_right (le_abs_self ..) (by positivity)) (mul_le_mul_of_nonneg_right (le_abs_self ..) (by positivity))
end YM.RG08.Reflect
