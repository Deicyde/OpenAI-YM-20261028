import YM.RG08.Canon.Sling
/-! # Canon fixed centered integrals obey same expansion requests in
 tilted Mössbauer orientation. No asymptotic interval constants reported
 here: τ and geometry paid once per step. Just producing equalities. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter Set Metric MeasureTheory YM.PertExtension.Series.Tested
open YM.PertExtension.Series.Radial YM.PertExtension.Chart RG08.Reflect
open scoped BigOperators Topology Real ContDiff Classical
variable (G : Gauge) (U : Type) [Fintype U]
variable {D : Precision.ChartRatio G}
local notation "E" => U → G.Color
local notation "Z" => (U → G.Color) × ℝ
local notation "T" => tangent G U
local notation "Ω" => physical G U
variable (L : ℝ→(U→G.Color)≃L[ℝ](U→G.Color)) (b : ℝ → U→G.Color)
variable (V : ℝ→(U→G.El)→ℝ) (K f : ((U→G.Color)×ℝ)→ℝ) (w : ℝ→ℝ)

omit [Fintype U] in
lemma track_plate (t : ℝ)(x : E) : track G U L b (t•plates G U x)=t • L t x + b t := by simp [track,plates]
lemma stadium_starts (P : Precision.LocalRatio D) (n : ℕ) (he:ContDiffAt ℝ ω K 0) (hK : Measurable K)
    (hp : YM.PertExtension.Series.Radial.Stationary f)(hf : Measurable f)
    (h : ∃ δ>0,∀ u:Z,δ*‖u‖^2 ≤ jet f 2 u)
    (hv : ∀ᶠ t in 𝓝[>]0, Measurable (V t))
    (hx : ContinuousAt (fun p:Z => L p.2 p.1) 0) (hy : ContinuousAt (fun p:Z => (L p.2).symm p.1) 0) (hb : ContinuousAt b 0) (hz : b 0=0)
    (hm : ∃ s∈𝓝 (0:Z),∀ᶠ t : ℝ in 𝓝[>]0,∀ x:E,(t•plates G U x)∈ s →
          YM.PertExtension.Series.Radial.projection K f t (plates G U x) = w t*(|swing (L t)| *
            (jacobian D (t•L t x+b t)*V t (expLinks G U (t•L t x+b t))))) :
    ∃ s ∈ 𝓝 (1:U→G.El), ∀ A : ℝ → Set (U→G.El), (∀ᶠ t in 𝓝[>] 0, MeasurableSet (A t) ∧ A t⊆s) →
      (∃ y ∈ 𝓝 1,∀ᶠ t in 𝓝[>] 0,y⊆A t) →
      Fit (n+1) (fun t=> w t*((t^Module.finrank ℝ (E))⁻¹*(∫ x in A t, V t x ∂Ω))) (peval (moment (hold G U) K f) n) := by
  obtain ⟨δ,hδ,hB⟩:= localized (hold G U) (he.of_le le_top) hK hf hp h n
  obtain ⟨s,hS,hP⟩:=hm
  obtain ⟨κ,hκ,hD⟩:= track_piece G U L b hz hb hy (ball 0 δ∩s) (inter_mem (ball_mem_nhds _ hδ) hS)
  let r:=min κ ((small G D)/2)
  have hr : 0<r := lt_min hκ (half_pos (Ratio.small_pos P))
  have hR:r<small G D:= (min_le_right ..).trans_lt (half_lt_self (Ratio.small_pos P))
  refine ⟨chamber G U r,chambers G U hr,fun A hQ ⟨y,hW,hT⟩=>?_⟩
  let S:= stadium G U L b r δ A
  have hi (t) (h : MeasurableSet (A t)) : MeasurableSet (S t):= stadium_meas _ _ _ _ h r δ
  obtain ⟨v,hL,hN⟩:=stadium_take G U L b (A:=A) hW hδ hr hx hz hb
  refine bill_flip (hB δ hδ le_rfl S (hQ.mono fun t ⟨h,_⟩=>⟨hi _ h, inter_subset_left⟩) ⟨v,hL,hT.mono fun t he=> hN t he⟩) ?_
  filter_upwards [hD,hP,eventually_pos,hQ,hv] with t ht ht' hT₀ ⟨hF,hX⟩ hM
  let X:=A t
  have HE : (∫ x in A t, V t x ∂Ω)=∫ x in ball 0 r, jacobian D x* (X.indicator (V t) (expLinks G U x)) ∂T := by
    rw [← Ratio.chamber_integral P (X.indicator (V t)) (hM.indicator hF) hR hr, integral_indicator hF, Measure.restrict_restrict_of_subset hX]
  rw [Pi.sub_apply,Pi.sub_apply]; congr 1
  change (∫ p in S t,YM.PertExtension.Series.Radial.projection K f t p ∂hold G U)=_
  rw [HE,← integral_indicator (μ:=T) (s:=ball 0 r) isOpen_ball.measurableSet (f:=fun x => jacobian D x * X.indicator (V t) (expLinks G U x)),gain G U (b t) _ _ hT₀.le,takeL G U (L t),← integral_const_mul (w t), illuminate G U (projection_meas hK hf ..) (S t) (hi t hF)]
  apply integral_congr_ae; apply Eventually.of_forall
  intro x
  dsimp only [plates]
  by_cases hg:t•L t x+b t∈Metric.ball 0 r
  · have hh' := ht x (by rw [track_plate]; exact (ball_subset_ball (min_le_left ..)) hg)
    rw [indicator_of_mem hg]
    by_cases hx:expLinks G U (t•L t x+b t)∈A t
    · rw [indicator_of_mem (s:=X) hx,indicator_of_mem (s:=S t) (show (x,(1:ℝ))∈ S t from ⟨hh'.1, Or.inr ⟨hg,hx⟩⟩)]; exact ht' x hh'.2
    rw [indicator_of_notMem (s:=X) hx, indicator_of_notMem (s:=S t) (show (x,(1:ℝ))∉ S t from fun h=> hx ((h.2.resolve_left (not_not_intro rfl)).2))]; ring
  rw [indicator_of_notMem hg, indicator_of_notMem (s:=S t) (show (x,(1:ℝ))∉ S t from fun h=>hg ((h.2.resolve_left (not_not_intro rfl)).1)), mul_zero,mul_zero]

-- do not request measurable arbitrary analytic choice standins; can switch to any
lemma stadium_rules (P : Precision.LocalRatio D) (n : ℕ) (he:ContDiffAt ℝ ω K 0) (hk : ContDiffAt ℝ ω f 0)
    (hp : YM.PertExtension.Series.Radial.Stationary f)
    (h : ∃ δ>0,∀ u:Z,δ*‖u‖^2 ≤ jet f 2 u)
    (hv : ∀ᶠ t in 𝓝[>]0, Measurable (V t))
    (hx : ContinuousAt (fun p:Z => L p.2 p.1) 0) (hy : ContinuousAt (fun p:Z => (L p.2).symm p.1) 0) (hb : ContinuousAt b 0) (hz : b 0=0)
    (hm : ∃ s∈𝓝 (0:Z),∀ᶠ t : ℝ in 𝓝[>]0,∀ x:E,(t•plates G U x)∈ s →
          YM.PertExtension.Series.Radial.projection K f t (plates G U x) = w t*(|swing (L t)| *
            (jacobian D (t•L t x+b t)*V t (expLinks G U (t•L t x+b t))))) :
    ∃ s ∈ 𝓝 (1:U→G.El), ∀ A : ℝ → Set (U→G.El), (∀ᶠ t in 𝓝[>] 0, MeasurableSet (A t) ∧ A t⊆s) →
      (∃ y ∈ 𝓝 1,∀ᶠ t in 𝓝[>] 0,y⊆A t) →
      Fit (n+1) (fun t=> w t*((t^Module.finrank ℝ (E))⁻¹*(∫ x in A t, V t x ∂Ω))) (peval (moment (hold G U) K f) n) := by
  obtain ⟨R,hR,hT⟩:=linings he; obtain ⟨F,hF,hS⟩:=linings hk
  have ht : ContDiffAt ℝ ω F 0 := hk.congr_of_eventuallyEq hS
  have hC : ContDiffAt ℝ ω R 0 := he.congr_of_eventuallyEq hT
  have hD (n) : jet f n=jet F n := by funext i; unfold jet; rw [(hS.iteratedFDeriv ℝ _).eq_of_nhds]
  have hf : YM.PertExtension.Series.Radial.Stationary F := by
    rcases hp with ⟨a,z,v⟩
    exact ⟨a.congr_of_eventuallyEq hS,hS.eq_of_nhds.trans z,fun i=> by rw [← hD,v i]⟩
  have hW (p:Z)(i : ℕ) : normTerm R F i p=normTerm K f i p := by
    refine aspiredV (n:=i) (Fit.supply ?_ _) (ink_cross hf (hC.of_le le_top) p) (ink_cross hp (he.of_le le_top) p) le_rfl
    have hw : Tendsto (fun t:ℝ=> t • p) (𝓝[>]0) (𝓝 0) := by
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      simpa using (show Continuous (fun t:ℝ=> t • p) by fun_prop).tendsto (0:ℝ)
    filter_upwards [hw.eventually hS,hw.eventually hT] with t he hx; rw [projection_eq,projection_eq,hx,he]
  rw [show moment (hold G U) K f=moment (hold G U) R F from funext fun i=> by unfold moment; simp_rw [hW]]
  refine stadium_starts G U L b V R F w P n hC hR hf hF (by rw [← hD]; exact h) hv hx hy hb hz ?_
  obtain ⟨s,hH,HH⟩:=hm; refine ⟨{x|x∈s∧R x=K x ∧ F x=f x},?_ ,?_⟩
  · exact (show ∀ᶠ (x:Z) in 𝓝 0,x∈s from hH).and (hT.and hS)
  exact HH.mono fun t ht x hx=> by
    rw [← ht x hx.1,projection_eq,projection_eq,hx.2.1,hx.2.2]
end YM.RG08.Canon
