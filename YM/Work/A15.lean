import YM.Work.A15.Transfer

/-!
# Averaging the stress

In the finite-dimensional label spaces. In particular all the D, conservation,
and angular-shell tests we pass through the average operate on these very
spaces; no implicit covariance or estimate on choices of representatives.
See also `Tensor`, `Shell`, `Transfer` here for the component action, sense of
flux and verification at each point of the group respectively.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A15

open MeasureTheory Table
open scoped BigOperators Topology Matrix.Norms.Frobenius

variable {G : Gauge} {L : Register G} {S : Table L}

theorem normalize_flux {X : Rotation S} {V : DiffPlan S} {p : Climb.Parts S}
    {Y : Ward.SpinRows S} (H : S.Hierarchy) (J : S.Stress) (c : ℝ)
    (h : Climb.Crystal H V J p Y c) (e : X.lie = c⁻¹ • Y) :
    StressLaws S (((c⁻¹ : ℝ) : ℂ) • J) V.deriv X.lie where
  translation := by
    intro n x hx q χ w b d B
    have he : p d b B = (c : ℂ) • V.deriv d b B :=
      Eq.trans (congrArg (fun f : Climb.Vector d S => f b B) (h.sizes d))
        (RCLike.real_smul_eq_coe_smul (K := ℂ) c _)
    rw [← translationFlux_apply hx w H.smooth, map_smul, translationFlux_apply,
      h.pre.local_.raw.translation hx q w, ← front_apply, ← map_smul, he, Complex.ofReal_inv,
      inv_smul_smul₀, front_apply]
    exact_mod_cast h.positive
  rotation := by
    intro n x hx q χ w g d B
    have he : X.lie d g B = ((c⁻¹ : ℝ) : ℂ) • Y d g B := by
      rw [e]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) c⁻¹ _
    rw [← angularFlux_apply hx w H.smooth, map_smul, angularFlux_apply,
      h.pre.local_.raw.rotation hx q w, ← front_apply, ← map_smul, ← he, front_apply]

section Haar

-- Parallel to `Gauge.compactGaugeU` / `Gauge.probHaar`. Here the group for
-- the average is orthogonal (on E4), *not* the gauge group.
private lemma sq_frobenius (A : M4) : ‖A‖ ^ 2 = (A * star A).trace := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
  · simp_rw [Real.rpow_two, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
      Real.norm_eq_abs, sq_abs, pow_two]
  simp_rw [Real.rpow_two]
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem compact_ortho : CompactSpace Ortho := by
  refine isCompact_iff_compactSpace.mp ?_
  letI : ProperSpace M4 := FiniteDimensional.proper ℝ _
  refine (isCompact_closedBall (0 : M4) 2).of_isClosed_subset isClosed_unitary ?_
  intro A h
  have hm := sq_frobenius A
  rw [Matrix.mem_unitaryGroup_iff.mp h, Matrix.trace_one, Fintype.card_fin] at hm
  rw [Metric.mem_closedBall, dist_zero_right]
  norm_num at hm
  nlinarith [hm]

attribute [local instance] compact_ortho

local instance : SecondCountableTopology Ortho := by
  haveI : SecondCountableTopology M4 :=
    inferInstanceAs (SecondCountableTopology (Axis → Axis → ℝ))
  exact inferInstanceAs
    (SecondCountableTopology ↥((Matrix.unitaryGroup Axis ℝ : Set M4)))

local instance : MeasurableSpace Ortho := borel Ortho
local instance : BorelSpace Ortho := ⟨rfl⟩

private def allOrthogonal : TopologicalSpace.PositiveCompacts Ortho :=
  ⟨⟨Set.univ, isCompact_univ⟩, by simp⟩

private def μ : Measure Ortho := Measure.haarMeasure allOrthogonal
local instance : μ.IsHaarMeasure := by unfold μ; infer_instance
local instance : IsProbabilityMeasure μ :=
  ⟨@Measure.haarMeasure_self Ortho _ _ _ _ _ allOrthogonal⟩

/-- Component-and-label average, with Haar of total mass one. -/
def averageStress (X : Rotation S) (J : S.Stress) := ∫ K : Ortho, rotateStress X K J ∂μ

variable {V : DiffPlan S} {H : S.RealSpin} {X : Rotation S} (h : X.Laws V H) (J : S.Stress)
include h

private lemma orbit_integrable : Integrable (fun K : Ortho => rotateStress X K J) μ := by
  have ent (a b : Axis) : Continuous fun K : Ortho => K.val a b := by
    have hv : Continuous fun K : Ortho => (K.val : Axis → Axis → ℝ) := continuous_subtype_val
    exact (continuous_apply _).comp ((continuous_apply _).comp hv)
  have hf : Continuous fun K => rotateStress X K J := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp_rw [rotateStress_apply]
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      (Complex.continuous_ofReal.comp ((ent a i).mul (ent b j))).smul ?_
    exact h.spin 4 (J i j)
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

private lemma map_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (P : S.Stress →ₗ[ℝ] E) :
    P (averageStress X J) = ∫ K : Ortho, P (rotateStress X K J) ∂μ := by
  exact ((LinearMap.toContinuousLinearMap P).integral_comp_comm (orbit_integrable h J)).symm

private theorem average_fixed (K : Ortho) :
    rotateStress X K (averageStress X J) = averageStress X J := calc
  _ = ∫ P : Ortho, rotateStress X K (rotateStress X P J) ∂μ :=
    map_average h J ((rotateStress X K).restrictScalars ℝ)
  _ = ∫ P : Ortho, rotateStress X (K*P) J ∂μ := by simp_rw [rotate_mul h]
  _ = averageStress X J :=
    (measurePreserving_mul_left μ K).integral_comp (Homeomorph.mulLeft K).measurableEmbedding
      (fun P : Ortho => rotateStress X P J)

theorem tensorial_average : Tensorial X (averageStress X J) :=
  tensorial_of_fixed X _ (average_fixed h J)

-- For keeping the real form. No Hilbert norm on the quotient is needed.
omit h in
private def realConjugateComponent (H : S.RealSpin) (a b : Axis) : S.Stress →ₗ[ℝ] S.Field 4 where
  toFun U := S.conj H 4 (U a b)
  map_add' u v := (S.conj H 4).map_add (u a b) (v a b)
  map_smul' r u := by
    change S.conj H 4 (r • u a b) = r • S.conj H 4 (u a b)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), map_smulₛₗ]
    simp

private lemma average_component (a b : Axis) :
    averageStress X J a b = ∫ K : Ortho, rotateStress X K J a b ∂μ :=
  map_average h J ((component (S := S) a b).restrictScalars ℝ)

theorem conserved_average (c : Conserved V H J) : Conserved V H (averageStress X J) where
  symmetric a b := by
    rw [average_component h, average_component h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun K =>
      (rotate_conserved h K J c).symmetric a b)
  real a b := calc
    _ = ∫ K : Ortho, S.conj H 4 (rotateStress X K J a b) ∂μ :=
      map_average h J (realConjugateComponent H a b)
    _ = ∫ K : Ortho, rotateStress X K J a b ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun K =>
        (rotate_conserved h K J c).real a b)
    _ = _ := (average_component h J a b).symm
  divergence b := by
    calc
      _ = divergenceMap V b (averageStress X J) := (divergenceMap_apply V b _).symm
      _ = ∫ K : Ortho, divergenceMap V b (rotateStress X K J) ∂μ :=
        map_average h J ((divergenceMap V b).restrictScalars ℝ)
      _ = ∫ _ : Ortho, (0 : S.Field (4+1)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun K =>
          (divergenceMap_apply V b _).trans ((rotate_conserved h K J c).divergence b))
      _ = 0 := integral_zero _ _

omit h in
theorem stressLaws_average (A : Bid.A10) (hc : S.Hierarchy) (u : X.Laws V hc.spin)
    (xO : X.Oriented S) (c : StressLaws S J V.deriv X.lie) :
    StressLaws S (averageStress X J) V.deriv X.lie where
  translation := by
    intro n x hx q χ w b d B
    calc
      _ = translationFlux hx w hc.smooth q B b (averageStress X J) :=
        (translationFlux_apply hx w hc.smooth q B b _).symm
      _ = ∫ K : Ortho, translationFlux hx w hc.smooth q B b (rotateStress X K J) ∂μ :=
        map_average u J ((translationFlux hx w hc.smooth q B b).restrictScalars ℝ)
      _ = ∫ _ : Ortho, S.useAt S x (Fin.cons ⟨d+1,V.deriv d b B⟩ q) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun K =>
          (translationFlux_apply hx w hc.smooth q B b _).trans
            ((rotate_flux A hc u xO K J c).translation hx q w b d B))
      _ = _ := by simp
  rotation := by
    intro n x hx q χ w g d B
    calc
      _ = angularFlux hx w hc.smooth q B g (averageStress X J) :=
        (angularFlux_apply hx w hc.smooth q B g _).symm
      _ = ∫ K : Ortho, angularFlux hx w hc.smooth q B g (rotateStress X K J) ∂μ :=
        map_average u J ((angularFlux hx w hc.smooth q B g).restrictScalars ℝ)
      _ = ∫ _ : Ortho, S.useAt S x (Fin.cons ⟨d,X.lie d g B⟩ q) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun K =>
          (angularFlux_apply hx w hc.smooth q B g _).trans
            ((rotate_flux A hc u xO K J c).rotation hx q w g d B))
      _ = _ := by simp
end Haar

/-- Retune the unnormalized stress coming with the crystal, on the given S. -/
theorem answer : YM.Bid.A15 := by
  intro A G L S H V _incl _der _orient X hX xO J p Y c h e
  let J₀ := ((c⁻¹ : ℝ) : ℂ) • J
  refine ⟨averageStress X J₀, ?_, tensorial_average hX J₀, ?_⟩
  · exact conserved_average hX J₀ (conserved_real_smul J h.pre.local_.tensor c⁻¹)
  · exact stressLaws_average J₀ A H hX xO (normalize_flux H J c h e)

end YM.Work.A15
