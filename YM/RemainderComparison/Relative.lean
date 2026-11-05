import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Token.Fluent
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orin

/-!
# Left-window derivatives of the actual conditional integral

Relative rather than absolute denominator cost. Freeze the entire fine input (including
hard masks), coupling and geometry of this one step. Differentiate in a chart in the
coarse field. Each term, *including its true likelihood*, can be bounded relative to
itself, because the kernel is a nonnegative mixture and the potentially huge untouched
part of each exponent is constant in these derivatives. Meristem gives all finite orders
post-integration, even on an output mask seam. Thus prescribed input portions (including
signed insertions) priced at the same conditional integral can use that price rather than
pay an exponential in the volume to divide by the normalization.

Cost polynomial in the inverse squared coupling β for fixed derivative order, per-link
jet radius and NUMBER of ACTUALLY changing coarse links (arbitrary realization and period).
This is a rough estimate for the normalization slot of a comparison, *not* estimating
the difference from the WilsonX coefficients. There is no complex-coupling or moving-threshold
differentiation here.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Relative
open Function Filter Lattice RG Wilson MeasureTheory Push Push.Uniform
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} (S : StepData c f) (β : ℝ)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {j : ℕ} {V : E → Config G c} {x : E}

-- test the denominator on a spine. Outside the spine the data are held fixed,
-- not integrated or differentiated separately.
structure Window (o : Finset (Edge (Site c))) (V : E → Config G c) (x : E)
    (j : ℕ) (v : ℝ) : Prop where
  cost : 0 ≤ v
  still e : e ∉ o → ∀ y, V y e = V x e
  here : ∀ᶠ y in 𝓝 x, ∀ e ∈ o, Allows j (fun t => G.mat (V t e)) y v

def load (G : Gauge) (k : KernelChoices) (β : ℝ) (n j : ℕ) (v : ℝ) :=
  ‖β‖ * k.penalty * n * priceCost G (2^j * v * G.colorScale)

/-- Cost per unit of the (unnormalized) input column at the actual conditional
integral. Does not divide by the vacuum or include the phase here. -/
def score (G : Gauge) (k : KernelChoices) (β : ℝ) (n j : ℕ) (v expCost : ℝ) :=
  let a := load G k β n j v
  Lantern.clump j (a+a) expCost

lemma score_nonneg (S : StepData c f) (β : ℝ) (n j : ℕ) {v z : ℝ} (hp : 0 ≤ v)
    (he : Brush j z 1 Real.exp 0) : 0 ≤ score G S.kernel β n j v z := by
  have hv := S.kernel.penalty_pos
  have hz := he.nonneg
  unfold score Lantern.clump load priceCost Gauge.colorScale
  dsimp only
  positivity

section noise
variable {o : Finset (Edge (Site c))} {v z : ℝ}
local notation "W" => (score G S.kernel β o.card j v z)

lemma noise_deriv (Q : Config G c) (hout : ∀ e ∉ o, ∀ y, V y e = V x e)
    (hV : ∀ e ∈ o, Allows j (fun t => G.mat (V t e)) x v) (he : Brush j z 1 Real.exp 0) :
    Brush j (W * S.noise β Q (V x)) 1 (fun y => S.noise β Q (V y)) x := by
  let a := load G S.kernel β o.card j v
  let p (y : E) e := G.price (V y e*(Q e)⁻¹)
  let Δ (y : E) := -β*S.kernel.penalty*∑ e ∈ o, p y e
  let σ (e : Edge (Site c)) := (S.penaltyZ β G)⁻¹
  let t := (∏ e∈o, σ e) * ∏ e∈oᶜ, (σ e * S.penaltyWeight β (V x e * (Q e)⁻¹))
  have hh y : S.noise β Q (V y)=t * Real.exp (Δ y) := by
    unfold StepData.noise
    rw [← Finset.prod_mul_prod_compl o]
    have hw : (∏ b ∈ oᶜ, ((S.penaltyZ β G)⁻¹ * S.penaltyWeight β (V y b * (Q b)⁻¹))) =
        ∏ b ∈ oᶜ, (σ b * S.penaltyWeight β (V x b * (Q b)⁻¹)) := by
      refine Finset.prod_congr rfl fun e he' => ?_
      rw [hout e (Finset.mem_compl.mp he')]
    rw [hw]; unfold t Δ
    rw [mul_right_comm (∏ e ∈ o, σ e), Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
    rfl
  have ht : 0 ≤ t := by
    have hs (e : Edge (Site c)) : 0 ≤ σ e := (inv_pos.mpr (S.penaltyZ_pos _)).le
    unfold t; exact mul_nonneg (Finset.prod_nonneg fun b _=> hs b)
      (Finset.prod_nonneg fun b _=> mul_nonneg (hs b) (Real.exp_nonneg _))
  have hf (e) (h : e ∈ o) : Allows j (fun x=> p x e) x (priceCost G (2^j*v*G.colorScale)) := by
    have hc := allows_const (n:=j) x (show ‖G.mat ((Q e)⁻¹)‖ ≤ G.colorScale from le_of_eq (Gauge.unitary_frob (G.mat_mul_star _)))
    exact Allows.price (f:=fun y => V y e * (Q e)⁻¹) ((hV e h).times (f:=fun y => V y e) (g:=fun _=> (Q e)⁻¹) hc)

  have hz' := (allows_sum (s:=o) hf).smul (-β*S.kernel.penalty)
  have ha : Allows j Δ x a := by
    simpa only [a,Δ,load,Finset.sum_const,nsmul_eq_mul,abs_mul,abs_neg,← Real.norm_eq_abs (r:=β),abs_of_pos S.kernel.penalty_pos,smul_eq_mul,mul_assoc] using hz'
  have hΔ : Brush j a 1 Δ x := Brush.offer.2 ⟨ha.analytic.of_le le_top,ha.2⟩
  have hp := Token.seasons Δ ht x hΔ he
  rw [hh x,funext hh]
  exact hp
end noise

section varying
variable {o : Finset (Edge (Site c))} {v z : ℝ}
local notation "W" => (score G S.kernel β o.card j v z)

lemma density_deriv (hV : Window o V x j v) (he : Brush j z 1 Real.exp 0) :
    ∀ᶠ y in 𝓝 x, ∀ U : Config G f, Brush j (W * S.density β U (V y)) 1
        (fun y => S.density β U (V y)) y := by
  filter_upwards [hV.here] with y hy U
  unfold StepData.density
  rw [Finset.mul_sum]
  refine Brush.spree _ _ _ zero_le_one fun k _=> ?_
  have hh := (noise_deriv S β (S.prediction U k) (V:=V) (x:=y) (o:=o)
    (fun e hi y'=> (hV.still e hi y').trans (hV.still e hi y).symm) hy he).smul (S.likelihood U k)
  rw [Real.norm_of_nonneg (S.likelihood_pos ..), mul_left_comm] at hh
  exact hh

-- vector version of `Meristem.points`, pays no dimension factor
variable [FiniteDimensional ℝ E] {F α : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace α]
lemma test_domination {U : E → α → F} {x : E} {μ : Measure α} {M : α → ℝ}
    (hm : Integrable M μ)
    (hp : ∀ᶠ y in 𝓝 x, ∀ i, Brush j (M i) 1 (fun y=> U y i) y)
    (hq : ∀ᶠ y in 𝓝 x, StronglyMeasurable (U y)) : Meristem U x μ j := by
  obtain ⟨O,hO,ho,hx⟩:= _root_.mem_nhds_iff.mp (hp.and hq)
  have ht y (hy:y∈O) : (∀ i, Brush j (M i) 1 (fun y=> U y i) y) ∧ StronglyMeasurable (U y) := hO hy
  refine ⟨O,ho.mem_nhds hx,ae_of_all _ (fun _ y h=>(ht y h).1 _ |>.1),fun k hk=> ⟨M,hm,fun y hy=> ?_,ae_of_all _ fun i y hy=>?_⟩⟩
  · exact (Meristem.legs (f:=Function.swap U) ho (fun i t h=> ((ht t h).1 i).smooth)
      (fun i hi=> (ht i hi).2) hk hy).aestronglyMeasurable
  exact (Brush.offer.1 ((ht _ hy).1 i)).inside k hk

variable [CompleteSpace F]

/-- Derivatives under the actual common-measure push, for *any fixed* strongly measurable
integrable fine insertion coefficient (no healthy-domain restriction, can be applied to
fixed mask indicators too). Bound uses the zeroth push of its absolute majorant; if positive
scalar, recovers a relative bound without taking a diagram-by-diagram inverse. -/
theorem absolute_push (H : Config G f → F) (hH : Integrable H (prior G f))
    (hm : StronglyMeasurable H) (hk : S.IsKernel β G)
    (hV : Window o V x j v) (he : Brush j z 1 Real.exp 0) :
    Brush j (W * S.push β (fun i=> ‖H i‖) (V x)) 1 (fun y=> S.push β H (V y)) x := by
  let k := W
  let F' y i := S.density β i (V y) • H i
  have hp : 0 ≤ k := score_nonneg S β _ _ hV.cost he
  have hv : ∀ᶠ y in 𝓝 x, ∀ i, Brush j (k * S.density β i (V y) * ‖H i‖) 1 (fun y => F' y i) y := by
    filter_upwards [density_deriv S β hV he] with y hy i
    let L : ℝ →L[ℝ] F := (ContinuousLinearMap.id ℝ ℝ).smulRight (H i)
    have hq : ‖L‖ ≤ ‖H i‖ := ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      (fun a=> by change ‖a • H i‖ ≤ ‖H i‖ * ‖a‖; rw [norm_smul,mul_comm])
    have hl := (hy i).report L hq
    rw [mul_comm ‖H i‖] at hl
    exact hl
  obtain ⟨d,hd⟩:= hk.bound
  have hs y : Measurable (fun i=> S.density β i (V y)) := by
    change Measurable ((fun u : Config G f × Config G c => S.density β u.1 u.2) ∘ (fun i : Config G f => (i,V y)))
    have hy : Measurable (fun i : Config G f => (i,V y)) := measurable_id.prodMk measurable_const
    exact hk.meas.comp hy
  have hu : Meristem F' x (prior G f) j := test_domination (hH.norm.const_mul (k*d)) (hv.mono ?_)
      (Eventually.of_forall fun y=> ((hs y).stronglyMeasurable).smul hm)
  swap
  · intro y hy i
    exact (hy i).climb (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hd ..) hp) (norm_nonneg _)) le_rfl
  have h := (StepData.push_slice hk (V x) (fun i=> ‖H i‖) hH.norm).const_mul k
  unfold StepData.push
  refine hu.buds _ h zero_le_one (MeasureTheory.integral_const_mul ..).le (ae_of_all _ fun i=> ?_)
  rw [smul_eq_mul,← mul_assoc]
  exact hv.self_of_nhds i
end varying

section pivot
variable [FiniteDimensional ℝ E] {V : E → Config G c}
    {v θ1 θ2 z : ℝ} {x : E} {o : Finset (Edge (Site c))} (D : Config G f → ℝ)
    (hd : ∀ U, 0 ≤ D U) (hD : Integrable D (prior G f)) (hm : StronglyMeasurable D)
    (hk : S.IsKernel β G) (hV : Window o V x j v) (he : Brush j z 1 Real.exp 0)
local notation "W" => (score G S.kernel β o.card j v z)
local notation "d" => (fun y=> S.push β D (V y))

include S β hd hD hm hk hV he
lemma root : Brush j (W * d x) 1 d x := by
  have hp := absolute_push S β D hD hm hk hV he
  simp_rw [Real.norm_of_nonneg (hd _)] at hp
  exact hp

variable (hv : 0 < S.push β D (V x))
include hv
lemma log_pivot (hw : Brush j θ1 1 Real.log 1) :
    Brush j (Lantern.clump j W θ1) 1 (fun y=> Real.log (d y) - Real.log (d x)) x := by
  have H := root S β D hd hD hm hk hV he
  have hh := H.smul (d x)⁻¹
  rw [Real.norm_of_nonneg ((inv_pos.mpr hv).le),mul_left_comm, inv_mul_cancel₀ hv.ne',mul_one] at hh
  let F y := (d x)⁻¹ * d y
  refine (Lantern.composite (f:=F) hh (show Brush j θ1 1 Real.log (F x) from (inv_mul_cancel₀ hv.ne').symm ▸ hw)).shimmy ?_
  filter_upwards [H.smooth.continuousAt.eventually (lt_mem_nhds hv)] with y hy
  unfold comp F
  rw [Real.log_mul (inv_pos.mpr hv).ne' (ne_of_gt hy),Real.log_inv]; ring

/-- Relative precision with derivatives for the quotient operation,
valid also on output flagged V (though the zeroth relative input mass on the RHS may itself
cost there; it is explicit). No conversion to the history budgets by this statement alone. -/
theorem divide {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f₁ : Config G f → F) (h : Integrable f₁ (prior G f)) (hg : StronglyMeasurable f₁)
    (hs : Brush j θ2 1 (fun u : ℝ => u⁻¹) 1) :
    Brush j ((Lantern.clump j W θ2)* ((d x)⁻¹ * (W * S.push β (fun i=> ‖f₁ i‖) (V x))))
      2 (fun y=> (d y)⁻¹ • S.push β f₁ (V y)) x := by
  have hF := (absolute_push S β f₁ h hg hk hV he).smul ((d x)⁻¹)
  rw [Real.norm_of_nonneg (inv_pos.mpr hv).le] at hF
  have hh := (root S β D hd hD hm hk hV he).smul ((d x)⁻¹)
  rw [Real.norm_of_nonneg ((inv_pos.mpr hv).le),mul_left_comm, inv_mul_cancel₀ hv.ne',mul_one] at hh
  let f' y := (d x)⁻¹ * d y
  have hm' : f' x=1:= inv_mul_cancel₀ hv.ne'
  have h' := Lantern.composite (f:=f') hh (show Brush j θ2 1 (fun t:ℝ=>t⁻¹) (f' x) from hm'.symm ▸ hs)
  have hh := Brush.twins h' hF (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
  refine (hh.climb (mul_le_of_le_one_left (mul_nonneg h'.nonneg hF.nonneg) ContinuousLinearMap.opNorm_lsmul_le) (by norm_num : (1:ℝ)+1 ≤ 2)).shimmy ?_
  filter_upwards with y
  change _ = ((f' y)⁻¹) • ((d x)⁻¹ • S.push β f₁ (V y))
  unfold f'
  rw [smul_smul,mul_inv_rev,inv_inv,mul_assoc,mul_inv_cancel₀ hv.ne',mul_one]
end pivot
end YM.RemainderComparison.Relative
