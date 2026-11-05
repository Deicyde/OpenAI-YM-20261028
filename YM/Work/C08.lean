import YM.Analysis.Polydisc
import YM.Bid.Corners
import YM.Spark.Limit

/-!
# Strong real push and boost generator on Joint
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C08
open Function Set Filter MeasureTheory YM.Analysis Mink Boundary
open scoped ContDiff Topology BigOperators InnerProductSpace

section Affine

variable {Z X : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]

-- `Probe.ahead b (Probe.along A f)` is `fun x => f (A (x - b))`.

omit [FiniteDimensional ℝ X] in
private theorem jet_affine (b : X) (A : X ≃L[ℝ] X) (f : Probe X) (k : ℕ) (x : X) :
    Spark.jet x k (Probe.ahead b (Probe.along A f)) =
      (Spark.jet (A (x - b)) k f).compContinuousLinearMap fun _ => A.toContinuousLinearMap := by
  let L := A.toContinuousLinearMap
  change iteratedFDeriv ℝ k (fun z : X => (⇑f ∘ L) (z - b)) x = _
  rw [iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right (f.smooth k) (x - b) le_rfl]
  rfl

-- Cost of the polynomial weight is controlled by the inverse linear part and translation.
omit [FiniteDimensional ℝ X] in
private theorem size_affine_le (b : X) (A : X ≃L[ℝ] X) (f : Probe X) (i k : ℕ) :
    Probe.size i k (Probe.ahead b (Probe.along A f)) ≤
      (‖A.symm.toContinuousLinearMap‖ + ‖b‖) ^ i * ‖A.toContinuousLinearMap‖ ^ k *
        (2 ^ i * ((Finset.Iic (i,k)).sup (schwartzSeminormFamily ℂ X ℂ)) f) := by
  let c := ‖A.symm.toContinuousLinearMap‖ + ‖b‖
  have hc : 0 ≤ c := add_nonneg (norm_nonneg _) (norm_nonneg _)
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _ (by positivity) fun x => ?_
  let y := A (x-b)
  have hx : ‖x‖ ≤ c * (1 + ‖y‖) := calc
    ‖x‖ = ‖A.symm y + b‖ := by simp [y]
    _ ≤ ‖A.symm y‖ + ‖b‖ := norm_add_le _ _
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖y‖ + ‖b‖ := add_le_add_left
      (A.symm.toContinuousLinearMap.le_opNorm y) _
    _ ≤ c * (1 + ‖y‖) := by
      dsimp only [c]
      nlinarith [norm_nonneg A.symm.toContinuousLinearMap, norm_nonneg b, norm_nonneg y]
  have H : ‖Spark.jet x k (Probe.ahead b (Probe.along A f))‖ ≤
      ‖Spark.jet y k f‖ * ‖A.toContinuousLinearMap‖ ^ k := by
    rw [jet_affine]
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
      (Spark.jet y k f).norm_compContinuousLinearMap_le (fun _ => A.toContinuousLinearMap)
  rw [← Spark.Jet]
  calc
    _ ≤ (c*(1 + ‖y‖))^i * (‖Spark.jet y k f‖ * ‖A.toContinuousLinearMap‖ ^ k) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx _) H (norm_nonneg _) (by positivity)
    _ = c^i * ‖A.toContinuousLinearMap‖ ^ k * ((1 + ‖y‖)^i * ‖Spark.jet y k f‖) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℂ) (m:=(i,k)) le_rfl le_rfl f y) (by positivity)

/-- Schwartz continuity of precomposition by a continuously varying affine coordinate change. -/
theorem continuous_affine_probe (b : Z → X) (A : Z → X ≃L[ℝ] X) (f : Probe X)
    (hb : Continuous b)
    (hA : Continuous (fun p => (A p).toContinuousLinearMap))
    (hI : Continuous (fun p => (A p).symm.toContinuousLinearMap)) :
    Continuous (fun p => Probe.ahead (b p) (Probe.along (A p) f)) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  apply Spark.ready
  · intro k x
    rw [← nhds_prod_eq]
    have H : Continuous (fun s : Z × X => Spark.jet s.2 k (Probe.ahead (b s.1) (Probe.along (A s.1) f))) := by
      have ht : Continuous (fun s : Z × X => A s.1 (s.2 - b s.1)) :=
        (hA.comp continuous_fst).clm_apply (continuous_snd.sub (hb.comp continuous_fst))
      have hj : Continuous (fun s : Z × X => Spark.jet (A s.1 (s.2 - b s.1)) k f) :=
        ((f.smooth k).continuous_iteratedFDeriv (m := k) le_rfl).comp ht
      have hl : Continuous (fun s : Z × X => fun _ : Fin k => (A s.1).toContinuousLinearMap) :=
        continuous_pi (fun _ => hA.comp continuous_fst)
      let B := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
        (fun _ : Fin k => X) (fun _ => X) ℂ
      simp_rw [jet_affine]
      exact (B.cont.comp hl).clm_apply hj
    exact H.continuousAt.tendsto
  intro i k
  let C (z : Z) := (‖(A z).symm.toContinuousLinearMap‖ + ‖b z‖) ^ i *
    ‖(A z).toContinuousLinearMap‖ ^ k *
      (2 ^ i * ((Finset.Iic (i,k)).sup (schwartzSeminormFamily ℂ X ℂ)) f)
  have H : Continuous C := ((((hI.norm.add hb.norm).pow i).mul (hA.norm.pow k)).mul continuous_const)
  refine ⟨C p + 1, ?_⟩
  exact ((H.tendsto p).eventually (gt_mem_nhds (by linarith : C p < C p + 1))).mono
    fun z hz => (size_affine_le (b z) (A z) f i k).trans (le_of_lt hz)

end Affine

section FTC

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

attribute [local instance] Measure.Subtype.measureSpace

private theorem slope_error_evaluation (F D : ℝ → Probe X) (hD : Continuous D)
    (h : ∀ t : ℝ, ∀ x : X, HasDerivAt (fun s : ℝ => F s x) (D t x) t)
    (x : X) (t : ℝ) (ht : t ≠ 0) :
    (t⁻¹ • (F t - F 0) - D 0) x = ∫ u : Icc (0:ℝ) 1, (D (u.val * t) - D 0) x := by
  have hu (u : ℝ) : HasDerivAt (fun z : ℝ => F (z*t) x) (t • D (u*t) x) u := by
    have ht' : HasDerivAt (fun z : ℝ => z*t) t u := by
      simpa only [one_mul] using (hasDerivAt_id' u).mul_const t
    exact (h (u*t) x).scomp u ht'
  have hd : Continuous (fun u : ℝ => D (u*t) x) := by
    let P := (BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X ℂ)
    exact P.continuous.comp (hD.comp (continuous_id.mul continuous_const))
  have he : (∫ u in (0:ℝ)..1, t • D (u*t) x) = F t x - F 0 x := by
    simpa only [one_mul,zero_mul] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1) (fun u _ => hu u)
        (((continuous_const (y:=t)).smul hd).intervalIntegrable _ _))
  rw [intervalIntegral.integral_smul] at he
  change t⁻¹ • (F t x - F 0 x) - D 0 x = ∫ u : Icc (0:ℝ) 1, D (u.val*t) x - D 0 x
  rw [← he, inv_smul_smul₀ ht,
    integral_subtype measurableSet_Icc (fun u : ℝ => D (u*t) x - D 0 x),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (hd.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul]

/-- Pointwise derivative everywhere plus strong continuity of the derivative family suffice for
strong slope convergence. Integrate after evaluation on `[0,1]`. The slope itself is already a
Schwartz map, so `Spark.vig` applies to every jet: no Bochner integral in Schwartz is needed. -/
theorem probe_slope_of_pointwise (F D : ℝ → Probe X) (hD : Continuous D)
    (h : ∀ t : ℝ, ∀ x : X, HasDerivAt (fun s : ℝ => F s x) (D t x) t) :
    Tendsto (fun t : ℝ => t⁻¹ • (F t - F 0)) (𝓝[≠] 0) (𝓝 (D 0)) := by
  refine (Probe.tendN _ _ _).mpr fun i k ε he => ?_
  have hprob : IsProbabilityMeasure (volume : Measure ↥(Icc (0:ℝ) 1)) := ⟨by
    rw [Measure.Subtype.volume_univ nullMeasurableSet_Icc, Real.volume_Icc, sub_zero,
      ENNReal.ofReal_one]⟩
  have hhalf := half_pos he
  let B (t : ℝ) (u : ℝ) := Probe.size i k (D (u*t) - D 0)
  have hB (u : ℝ) : Tendsto (Function.uncurry B) ((𝓝[≠] 0) ×ˢ 𝓝 u) (𝓝 0) := by
    have hc : Continuous (Function.uncurry B) :=
      (Probe.cont_size i k).comp ((hD.comp (continuous_snd.mul continuous_fst)).sub continuous_const)
    have ht := hc.tendsto (0,u)
    rw [show Function.uncurry B (0,u) = 0 by simp [Function.uncurry,B,Probe.size], nhds_prod_eq] at ht
    exact ht.mono_left (Filter.prod_mono nhdsWithin_le_nhds le_rfl)
  filter_upwards [Spark.packing B (Icc (0:ℝ) 1) isCompact_Icc (fun u _ => hB u) _ hhalf,
    show ∀ᶠ t in 𝓝[≠] (0:ℝ), t ≠ 0 from self_mem_nhdsWithin] with t hbt ht
  let G (u : Icc (0 : ℝ) 1) := D (u.val*t) - D 0
  let R := t⁻¹ • (F t - F 0) - D 0
  change Probe.size i k R < ε
  have hc : Continuous G := (hD.comp (continuous_subtype_val.mul continuous_const)).sub continuous_const
  have hu (u : Icc (0:ℝ) 1) : Probe.size i k (G u) ≤ ε/2 :=
    le_of_lt (lt_of_le_of_lt (le_abs_self (B t u.val)) (hbt u.val u.property))
  apply lt_of_le_of_lt _ (half_lt_self he)
  refine SchwartzMap.seminorm_le_bound ℂ _ _ _ hhalf.le fun x => ?_
  rw [Spark.vig volume G (⇑R) hc (fun x => slope_error_evaluation F D hD h x t ht)]
  calc
    _ = ‖∫ u : Icc (0:ℝ) 1, ‖x‖^i • Spark.jet x k (G u)‖ := by
      rw [integral_smul, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ i)]
    _ ≤ ∫ _u : Icc (0:ℝ) 1, ε/2 := by
      apply norm_integral_le_of_norm_le (integrable_const _)
      apply Eventually.of_forall; intro u
      rw [norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ i)]
      exact (SchwartzMap.le_seminorm ℂ i k _ _).trans (hu u)
    _ = ε/2 := by simp

end FTC

section Joint

variable {n : ℕ}

-- lift linear coordinate changes (including their generators) across `Points n`
private def liftCoord (n : ℕ) : Coord →L[ℝ] (Points n →L[ℝ] Points n) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => LinearMap.toContinuousLinearMap
        { toFun := fun x => points fun i => A (x i)
          map_add' := fun x y => PiLp.ext fun i => map_add A (x i) (y i)
          map_smul' := fun r x => PiLp.ext fun i => map_smul A r (x i) }
      map_add' := fun _ _ => ContinuousLinearMap.ext fun _ => PiLp.ext fun _ => rfl
      map_smul' := fun _ _ => ContinuousLinearMap.ext fun _ => PiLp.ext fun _ => rfl }

theorem continuous_gpush (f : Joint n) : Continuous (fun p : Poincare => Joint.gpush n p f) := by
  apply continuous_affine_probe (fun p : Poincare => points fun _ : Fin n => p.b)
    (fun p => (Poincare.togetherL p.Λ n).symm)
  · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E4)).symm.continuous.comp
      (continuous_pi (fun _ => Poincare.continuousB))
  · exact (liftCoord n).continuous.comp (Lorentz.usual.comp Poincare.continuousL.inv)
  exact (liftCoord n).continuous.comp (Lorentz.usual.comp Poincare.continuousL)

private theorem cross_as_sum (x : Points n) (a : SpaceAxis) :
    liftCoord n (Ray.fromAxis a).crossT x =
      ∑ i : Fin n, (x i a.castSucc • Points.direction i timeAxis +
        x i timeAxis • Points.direction i a.castSucc) := by
  let e := Ray.fromAxis a
  apply PiLp.ext; intro j
  change e.crossT (x j) = (PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n => E4) j) _
  rw [map_sum, Finset.sum_eq_single j]
  · change e.crossT (x j) = ((x j a.castSucc • Points.direction j timeAxis +
        x j timeAxis • Points.direction j a.castSucc) j)
    simp only [Points.direction, PiLp.add_apply, PiLp.smul_apply, PiLp.single_eq_same]
    have he : position e.val 0 = basis a.castSucc := by
      apply PiLp.ext; intro i
      refine Fin.lastCases ?_ (fun b => ?_) i
      · change time _ = basis _ timeAxis
        rw [time_position,basis_eq, if_neg (Ne.symm (Fin.castSucc_ne_last _))]
      by_cases hb : b=a
      · simp [position,e,Ray.fromAxis,hb]
      simp [position,e,Ray.fromAxis,hb]
    simp only [Ray.crossT,he, Mink.clockL_at,_root_.add_apply,
      ContinuousLinearMap.smulRight_apply, Ray.alongL_at]
    rw [Ray.onAxis]; exact add_comm ..
  · intro i _ hi
    change ((x i a.castSucc • Points.direction i timeAxis +
        x i timeAxis • Points.direction i a.castSucc) j) = _
    simp [Points.direction,Ne.symm hi]
  simp

/-- Compute the signed (inverse placement!) infinitesimal move, pointwise. -/
theorem boost_pointwise_zero (f : Joint n) (a : SpaceAxis) (x : Points n) :
    HasDerivAt (fun i : ℝ => Joint.gpush n (Poincare.motion ((Ray.fromAxis a).boost i)) f x)
      ((-Bid.inclined a 0 f) x) 0 := by
  let e := Ray.fromAxis a
  let Y := fun s : ℝ => liftCoord n (Lorentz.act (e.boost (-s))) x
  have hY : Y 0 = x := by apply PiLp.ext; intro j; change Lorentz.act _ _ = _; simp
  have hE : HasDerivAt (fun s : ℝ => Lorentz.act (e.boost (-s))) (-e.crossT) 0 := by
    have ht : HasDerivAt (fun s : ℝ => Lorentz.act (e.boost s)) e.crossT (-(0:ℝ)) := by
      rw [neg_zero]; exact e.generator
    simpa only [Function.comp_def, neg_smul, one_smul] using
      (ht.scomp 0 (hasDerivAt_id' 0).neg)
  have hL := (liftCoord n).hasFDerivAt.comp_hasDerivAt 0 hE
  have hp : HasDerivAt Y (-(liftCoord n e.crossT x)) 0 := by
    let m := ContinuousLinearMap.apply ℝ (Points n) x
    have H := m.hasFDerivAt.comp_hasDerivAt 0 hL
    change HasDerivAt Y (m (liftCoord n (-e.crossT))) 0 at H
    simpa only [map_neg] using! H
  have hF := ((f.smooth 1).differentiable (by norm_num) (Y 0)).hasFDerivAt.comp_hasDerivAt 0 hp
  have hx : ⇑f ∘ Y = fun i : ℝ => Joint.gpush n (Poincare.motion (e.boost i)) f x := by
    funext i; rw [Joint.gpush_at,Function.comp_apply]; congr 1
    apply PiLp.ext; intro j
    change Lorentz.act (e.boost (-i)) (x j) = (Poincare.motion _ )⁻¹.sends _
    rw [Poincare.backwards, show (Poincare.motion (e.boost i)).b=0 from rfl, sub_zero]
    rw [← Ray.boost_neg]; rfl
  rw [hx, hY, map_neg, cross_as_sum, map_sum] at hF
  convert hF using 1
  · rfl
  rw [Bid.inclined, neg_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  simp [Bid.multiplier_test,Bid.realTerm, SchwartzMap.lineDerivOp_apply_eq_fderiv,
    Complex.real_smul]

theorem boost_pointwise (f : Joint n) (a : SpaceAxis) (x : Points n) (t : ℝ) :
    HasDerivAt (fun i : ℝ => Joint.gpush n (Poincare.motion ((Ray.fromAxis a).boost i)) f x)
      (Joint.gpush n (Poincare.motion ((Ray.fromAxis a).boost t)) (-Bid.inclined a 0 f) x) t := by
  let P := fun r : ℝ => Poincare.motion ((Ray.fromAxis a).boost r)
  let y := (P t)⁻¹.zusammen n x
  have h : HasDerivAt (fun i : ℝ => Joint.gpush n (P i) f y)
      ((-Bid.inclined a 0 f) y) (t - t) := by
    rw [sub_self]; exact boost_pointwise_zero f a y
  rw [Joint.gpush_at]
  change HasDerivAt (fun i : ℝ => Joint.gpush n (P i) f x) ((-Bid.inclined a 0 f) y) t
  rw [show (fun i : ℝ => Joint.gpush n (P i) f x) =
    (fun i : ℝ => Joint.gpush n (P (i-t)) f y) from funext fun i => by
      rw [Joint.gpush_at,Joint.gpush_at]
      congr 1
      have he : P i=P t * P (i-t) := by
        dsimp only [P]; rw [← Poincare.overL,← Ray.boost_add,add_sub_cancel ..]
      apply PiLp.ext; intro j
      change (P i)⁻¹.sends (x j)=(P (i-t))⁻¹.sends ((P t)⁻¹.sends (x j))
      rw [he, mul_inv_rev,Poincare.sends_mul]]
  exact h.comp_sub_const t t

private theorem boost_strong_slope (f : Joint n) (a : SpaceAxis) :
    Tendsto (fun i : ℝ => i⁻¹ • (Joint.gpush n (Poincare.motion ((Ray.fromAxis a).boost i)) f - f))
      (𝓝[≠] 0) (𝓝 (-Bid.inclined a 0 f)) := by
  let P := fun i : ℝ => Poincare.motion ((Ray.fromAxis a).boost i)
  let F := fun i : ℝ => Joint.gpush n (P i) f
  let D := fun i : ℝ => Joint.gpush n (P i) (-Bid.inclined a 0 f)
  have hc : Continuous D := (continuous_gpush _).comp (Poincare.continuousM.comp (Ray.fromAxis a).continuousBoost)
  have H := probe_slope_of_pointwise F D hc fun t x => boost_pointwise f a x t
  have he (g : Joint n) : Joint.gpush n (P 0) g=g := by
    ext1 x; simp [P,Poincare.zusammen]
  rw [show F 0=f from he _, show D 0 = -Bid.inclined a 0 f from he _] at H
  exact H

end Joint

theorem answer : YM.Bid.C08 :=
  ⟨fun _ f => continuous_gpush f, fun _ f a => boost_strong_slope f a⟩

end YM.Work.C08
