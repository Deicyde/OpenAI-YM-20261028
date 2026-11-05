import YM.Bid.Angular

/-!
# Limiting Casimir selection polynomial
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.A12

open Set Function Filter MeasureTheory Table Spin
open scoped Topology Matrix.Norms.Frobenius BigOperators

section Polynomial

/-- Finite-dimensional selection without choosing an eigensystem (or an
instance of a new inner product space). `reduce` just says that the zero
eigenvalue needs no generalized eigenvectors. Cayley-Hamilton and repeated
cancellation at zero suffice. -/
lemma selector_exists {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    (A : Y →ₗ[ℝ] Y) (reduce : ∀ y, A (A y) = 0 → A y = 0) :
    ∃ q : Polynomial ℝ, q.coeff 0 = 1 ∧ A * Polynomial.aeval A q = 0 := by
  -- Peel zero constant terms off any nonzero candidate until its
  -- constant term can be normalized. Keep an extra factor of `A`.
  have peel (p : Polynomial ℝ) : p ≠ 0 → A * Polynomial.aeval A p = 0 →
      ∃ q : Polynomial ℝ, q.coeff 0 = 1 ∧ A * Polynomial.aeval A q = 0 := by
    induction p using Polynomial.recOnHorner with
    | M0 => exact fun h => (h rfl).elim
    | MC p a hp ha ih =>
      intro _ h
      refine ⟨(p + Polynomial.C a) * Polynomial.C a⁻¹, ?_, ?_⟩
      · simp [hp, ha]
      rw [map_mul, ← mul_assoc, h, zero_mul]
    | MX p hp ih =>
      intro _ h
      rw [mul_comm p Polynomial.X, map_mul, Polynomial.aeval_X] at h
      apply ih hp
      ext1 y
      exact reduce (Polynomial.aeval A p y) (DFunLike.congr_fun h y)
  exact peel A.charpoly A.charpoly_monic.ne_zero (by rw [A.aeval_self_charpoly, mul_zero])

/-- List coefficients in the Horner convention of `Spin.evaluate`. -/
def polynomial (l : List ℝ) : Polynomial ℝ :=
  l.foldr (fun i s => Polynomial.C i + Polynomial.X * s) 0

lemma polynomial_cons (i : ℝ) (l : List ℝ) : polynomial (i::l) = Polynomial.C i + Polynomial.X * polynomial l := rfl

lemma polynomial_surj (q : Polynomial ℝ) : ∃ l : List ℝ, polynomial l = q := by
  induction q using Polynomial.recOnHorner with
  | M0 => exact ⟨[], rfl⟩
  | MC p a hp ha ih =>
    obtain ⟨l,rfl⟩ := ih
    cases l with
    | nil => exact ⟨[a], by simp [polynomial]⟩
    | cons b l =>
      exact ⟨(b + a)::l, by rw [polynomial_cons, polynomial_cons, map_add]; abel⟩
  | MX p hp ih =>
    obtain ⟨l,rfl⟩ := ih
    exact ⟨0::l, by rw [polynomial_cons]; simp [mul_comm]⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma evaluate_apply (A : Spin.End X) (x : Mat X) (l : List ℝ) :
    evaluate l A x = Polynomial.aeval (A.toLinearMap.restrictScalars ℝ) (polynomial l) x := by
  induction l with
  | nil => simp [evaluate, polynomial]
  | cons b l ih =>
    rw [polynomial_cons, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
    change (b:ℂ) • x + A (evaluate l A x) = b • x + A _
    rw [ih]
    exact congrArg (fun y => y + _) (RCLike.real_smul_eq_coe_smul (K := ℂ) b x).symm

lemma evaluate_apply_ker (A : Spin.End X) (x : Mat X) (hx : A x = 0) (l : List ℝ) :
    evaluate l A x = ((polynomial l).coeff 0:ℂ) • x := by
  induction l with
  | nil => simp [evaluate, polynomial]
  | cons b l ih =>
    change (b:ℂ) • x + A (evaluate l A x) = _
    simp [polynomial_cons, ih, hx]

end Polynomial

section Skew
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
variable [Fintype ι]

/-- Positivity and skewness need only be tested with a *real* form; it
need not compute the current norm. The sum used here is exactly with the
sign, powers, and indexing used in `wave`. -/
lemma works_of_skew (C : ι → Mat X)
    (B : Mat X →ₗ[ℝ] Mat X →ₗ[ℝ] ℝ)
    (hpos : ∀ x : Mat X, x ≠ 0 → 0 < B x x)
    (hs : ∀ (i : ι) (x y : Mat X), B (effect (C i) (C i) x) y + B x (effect (C i) (C i) y) = 0) :
    ∃ l : List ℝ, Works l C := by
  let D (i : ι) := effect (C i) (C i)
  let A := ∑ i, (D i)^2
  have hA (x : Mat X) : A x = ∑ i, D i (D i x) := by
    simp [A, pow_two]
  have hn (x : Mat X) : 0 ≤ B x x := by
    by_cases h : x = 0
    · simp [h]
    exact (hpos _ h).le
  have ker (x : Mat X) (hx : A x = 0) (i : ι) : D i x = 0 := by
    have ha : ∀ j, B (D j (D j x)) x = - B (D j x) (D j x) :=
      fun j => eq_neg_of_add_eq_zero_left (hs j (D j x) x)
    have he : B (A x) x = -∑ j, B (D j x) (D j x) := by
      rw [hA, map_sum]; simp [ha]
    by_contra h
    have hg : 0 < ∑ j, B (D j x) (D j x) :=
      Finset.sum_pos' (fun j _ => hn _) ⟨i, Finset.mem_univ _, hpos _ h⟩
    rw [hx, map_zero, LinearMap.zero_apply] at he
    exact hg.ne (by linarith)
  let f := A.toLinearMap.restrictScalars ℝ
  have hf (y : Mat X) (hy : f (f y) = 0) : f y = 0 := by
    change A (A y) = 0 at hy
    change A y = 0
    have hv (i : ι) : B (D i (D i y)) (A y) = 0 := by
      have he : B (D i (D i y)) (A y) + B (D i y) (D i (A y)) = 0 := hs i _ _
      rw [ker _ hy i, map_zero, add_zero] at he
      exact he
    have hB : B (A y) (A y) = 0 := calc
      _ = B (∑ i, D i (D i y)) (A y) := congrArg (fun t => B t (A y)) (hA y)
      _ = 0 := by rw [map_sum]; simp [hv]
    by_contra h
    exact (hpos _ h).ne' hB
  letI : FiniteDimensional ℝ (Mat X) := Module.Finite.trans ℂ _
  obtain ⟨q, hq, hm⟩ := selector_exists f hf
  obtain ⟨l,rfl⟩ := polynomial_surj q
  have hz (x : Mat X) : A (wave l C C x) = 0 := by
    change A (evaluate l A x) = 0
    rw [evaluate_apply]
    exact DFunLike.congr_fun hm x
  have hi (x : Mat X) (hx : A x = 0) : wave l C C x = x := by
    change evaluate l A x = x
    simp [evaluate_apply_ker _ _ hx, hq]
  refine ⟨l, ?_, hi 1 ?_, ?_⟩
  · ext1 x
    exact hi _ (hz x)
  · rw [hA]; simp [D, atAct]
  intro i
  ext1 x
  exact ker _ (hz x) i

end Skew

section Ortho

-- Cf. Gauge.compactGaugeU. Use the current real matrices (including
-- disconnected O) and the Frobenius scope.
theorem compact_ortho : CompactSpace Ortho := by
  apply isCompact_iff_compactSpace.mp
  letI : ProperSpace M4 := FiniteDimensional.proper ℝ M4
  apply (isCompact_closedBall (0:M4) (Real.sqrt (Fintype.card Axis))).of_isClosed_subset isClosed_unitary
  intro A h
  have row (i : Axis) : ∑ j, ‖A i j‖ ^ (2:ℝ) = (1:ℝ) := by
    have he : A * star A = (1:M4) := h.2
    have hp := congrArg (fun B : M4 => B i i) he
    simpa [Real.rpow_two, Real.norm_eq_abs, sq_abs, pow_two, Matrix.mul_apply,
      Matrix.star_eq_conjTranspose] using hp
  rw [Metric.mem_closedBall, dist_zero_right, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [row]; simp

lemma oneParameter_zero (g : Ortho.Skew) : Ortho.oneParameter g 0 = 1 := by
  letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ M4
  apply Subtype.ext
  change NormedSpace.exp ((0:ℝ) • g.val) = (1:M4)
  rw [zero_smul, NormedSpace.exp_zero]

lemma oneParameter_inv (g : Ortho.Skew) (t : ℝ) : (Ortho.oneParameter g t)⁻¹ = Ortho.oneParameter g (-t) := by
  letI : NormedAlgebra ℚ M4 := .restrictScalars ℚ ℝ M4
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change NormedSpace.exp (t • g.val) * NormedSpace.exp ((-t) • g.val) = (1:M4)
  rw [neg_smul]
  calc
    _ = NormedSpace.exp ((t • g.val) + -(t • g.val)) :=
      (NormedSpace.exp_add_of_commute (Commute.neg_right (Commute.refl (t • g.val)))).symm
    _ = 1 := by rw [add_neg_cancel, NormedSpace.exp_zero]

end Ortho

section Average
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- Averaging a coordinate dot product. Inverse action in the
integrand allows using just left Haar. All integrals use compact `Ortho`,
not the gauge Haar. -/
lemma invariant_form (ρ : Ortho → Y →ₗ[ℝ] Y)
    (hc : ∀ x, Continuous fun g => ρ g x)
    (h1 : ∀ x, ρ 1 x = x)
    (hm : ∀ g k x, ρ (g*k) x = ρ g (ρ k x)) :
    ∃ B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ, (∀ x y, B x y = B y x) ∧
      (∀ x, x ≠ 0 → 0 < B x x) ∧ ∀ k x y, B (ρ k x) (ρ k y) = B x y := by
  classical
  letI : CompactSpace Ortho := compact_ortho
  letI : MeasurableSpace Ortho := borel _
  letI : BorelSpace Ortho := ⟨rfl⟩
  let b := Module.finBasis ℝ Y
  let u (x y : Y) (g : Ortho) : ℝ := ∑ i, b.coord i (ρ g⁻¹ x) * b.coord i (ρ g⁻¹ y)
  have ht (x y : Y) : Continuous (u x y) :=
    continuous_finsetSum _ (fun i _ =>
      ((b.coord i).continuous_of_finiteDimensional.comp ((hc x).comp continuous_inv)).mul
        ((b.coord i).continuous_of_finiteDimensional.comp ((hc y).comp continuous_inv)))
  have hu (x y : Y) : Integrable (u x y) Measure.haar :=
    (ht _ _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let B0 (x y : Y) := ∫ g, u x y g ∂Measure.haar
  have hs (x y : Y) : B0 x y = B0 y x := by
    unfold B0; simp_rw [u, mul_comm]
  have ha (x y z : Y) : B0 (x+y) z = B0 x z + B0 y z := by
    have h (g) : u (x+y) z g = u x z g + u y z g := by
      unfold u; simp_rw [map_add, add_mul, Finset.sum_add_distrib]
    unfold B0; simp_rw [h]; exact integral_add (hu _ _) (hu _ _)
  have hw (c : ℝ) (x y : Y) : B0 (c • x) y = c • B0 x y := by
    have h (g) : u (c • x) y g = c * u x y g := by
      unfold u; simp_rw [map_smul, smul_eq_mul, mul_assoc, Finset.mul_sum]
    unfold B0; simp_rw [h]; exact integral_const_mul ..
  let B1 (x : Y) : Y →ₗ[ℝ] ℝ := {
    toFun := B0 x
    map_add' := fun y z => by rw [hs, ha, hs y, hs z]
    map_smul' := fun c y => by rw [hs, hw, hs y]; rfl }
  let B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ := {
    toFun := B1
    map_add' := fun x y => by ext1 z; exact ha ..
    map_smul' := fun c y => by ext1 z; exact hw .. }
  refine ⟨B, hs, fun x hx => ?_, fun k x y => ?_⟩
  · have hn (g : Ortho) : 0 ≤ u x x g := Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hp : 0 < u x x 1 := by
      obtain ⟨i,hi⟩ : ∃ i, b.coord i x ≠ 0 := by
        by_contra! h
        apply hx; apply b.ext_elem; intro i; simpa using h i
      unfold u; rw [inv_one]; simp_rw [h1]
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _) ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
    exact integral_pos_of_integrable_nonneg_nonzero (ht _ _) (hu _ _) hn hp.ne'
  have h (g : Ortho) : u (ρ k x) (ρ k y) g = u x y (k⁻¹*g) := by
    unfold u; simp only [← hm, mul_inv_rev, inv_inv]
  change (∫ g, u (ρ k x) (ρ k y) g ∂Measure.haar) = ∫ g, u x y g ∂Measure.haar
  simp_rw [h]; exact integral_mul_left_eq_self ..

lemma skew_of_invariant (ρ : Ortho → Y →ₗ[ℝ] Y) (h1 : ∀ x, ρ 1 x = x)
    (B : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ) (hB : ∀ k x y, B (ρ k x) (ρ k y) = B x y)
    (g : Ortho.Skew) (x y dx dy : Y)
    (hx : HasDerivAt (fun t => ρ (Ortho.oneParameter g t) x) dx 0)
    (hy : HasDerivAt (fun t => ρ (Ortho.oneParameter g t) y) dy 0) :
    B dx y + B x dy = 0 := by
  let F : Y →L[ℝ] Y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp B)
  have he := (F.hasFDerivAt.comp_hasDerivAt 0 hx).clm_apply hy
  change HasDerivAt (fun t => B (ρ (Ortho.oneParameter g t) x) (ρ (Ortho.oneParameter g t) y))
    (B dx (ρ (Ortho.oneParameter g 0) y) + B (ρ (Ortho.oneParameter g 0) x) dy) 0 at he
  simp_rw [hB, oneParameter_zero, h1] at he
  exact he.unique (hasDerivAt_const ..)

end Average
section Representation
variable {X ι : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
variable [Fintype ι]

/-- Selection on Hom for a finite-dimensional representation, for any
finite list of these derivatives. Differentiate the conjugation action
itself, so the operators tested are exactly `effect (C i) (C i)`. -/
theorem for_representation (R : Ortho → Mat X) (C : ι → Mat X) (g : ι → Ortho.Skew)
    (hc : Continuous R) (hr : R 1 = 1) (hm : ∀ k s, R (k*s) = R k * R s)
    (hv : ∀ i, HasDerivAt (fun t => R (Ortho.oneParameter (g i) t)) (C i) 0) :
    ∃ l : List ℝ, Works l C := by
  let Q (k : Ortho) : Spin.End X := ((ContinuousLinearMap.mul ℂ (Mat X)).flip (R k⁻¹)).comp
    (ContinuousLinearMap.mul ℂ _ (R k))
  let ρ (k : Ortho) := (Q k).toLinearMap.restrictScalars ℝ
  have hρ (k : Ortho) (x : Mat X) : ρ k x = R k * x * R k⁻¹ := rfl
  have h1 (x : Mat X) : ρ 1 x = x := by rw [hρ]; simp [hr]
  have ht (x : Mat X) : Continuous (fun k => ρ k x) :=
    (hc.mul continuous_const).mul (hc.comp continuous_inv)
  have hp (k s : Ortho) (x : Mat X) : ρ (k*s) x = ρ k (ρ s x) := by
    simp_rw [hρ, mul_inv_rev, hm, mul_assoc]
  letI : FiniteDimensional ℝ (Mat X) := Module.Finite.trans ℂ _
  obtain ⟨B, -, hpos, hB⟩ := invariant_form ρ ht h1 hp
  have hy (i : ι) (x : Mat X) : HasDerivAt (fun t => ρ (Ortho.oneParameter (g i) t) x)
      (effect (C i) (C i) x) 0 := by
    simp_rw [hρ]
    have he : HasDerivAt (fun t => R ((Ortho.oneParameter (g i) t)⁻¹)) (-(C i)) 0 := by
      -- NB here inverse is on Ortho
      simp_rw [oneParameter_inv]
      have hh : HasDerivAt (fun t => R (Ortho.oneParameter (g i) t)) (C i) (-(0:ℝ)) := by simpa using hv i
      have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id' _).neg
      simpa only [comp_def, neg_smul, one_smul] using hh.scomp 0 hn
    have hh := ((hv i).mul_const x).mul he
    simpa only [Pi.mul_def, oneParameter_zero, hr, inv_one, one_mul, mul_one, mul_neg, ← sub_eq_add_neg,
      atAct] using hh
  exact works_of_skew C B hpos (fun i x y => skew_of_invariant ρ h1 B hB (g i) x y _ _ (hy i x) (hy i y))

/-- Derivative version of `Dash.fit_plane`. -/
lemma fit_derivative (A : ℝ → X →ₗ[ℂ] X) (d : X →ₗ[ℂ] X)
    (hd : ∀ x : X, HasDerivAt (fun t => A t x) (d x) 0) :
    HasDerivAt (fun t => LinearMap.toContinuousLinearMap (A t))
      (LinearMap.toContinuousLinearMap d) 0 := by
  classical
  let b := Module.finBasis ℂ X
  let I := Fin (Module.finrank ℂ X)
  let F : (I → X) →ₗ[ℂ] Mat X := LinearMap.toContinuousLinearMap.toLinearMap.comp (b.constr ℂ).toLinearMap
  let M := (LinearMap.toContinuousLinearMap F).restrictScalars ℝ
  have he (g : X→ₗ[ℂ] X) : M (fun i => g (b i)) = LinearMap.toContinuousLinearMap g := by
    apply ContinuousLinearMap.coe_injective; exact b.ext fun i => b.constr_basis ..
  have hh : HasDerivAt (fun (t : ℝ) (i : I) => A t (b i)) (fun (i : I) => d (b i)) 0 :=
    hasDerivAt_pi.mpr fun i => hd _
  simpa only [Function.comp_def, he] using M.hasFDerivAt.comp_hasDerivAt 0 hh

/- Zero-dimensional edge of the above representation argument (the
finite fields in this ticket need not be assumed nonzero). -/
example : ∃ l : List ℝ, Works l (fun _ : Spin.Ind => (0 : Mat (Fin 0 → ℂ))) := by
  apply for_representation (fun _ => 1) _ Spin.K continuous_const rfl
  · simp
  intro i; exact hasDerivAt_const 0 _

-- And check the Horner convention on zero Lie maps with identity nonzero.
example : Works [1] (fun _ : Spin.Ind => (0 : Mat ℂ)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [wave, evaluate]
  · simp [wave, evaluate]
  intro i; ext1 x; simp [wave, evaluate, atAct]

end Representation

theorem answer : YM.Bid.A12 := by
  intro G L S T H h d
  let a (k : Ortho) := (T.act d k).toLinearMap
  let R (k : Ortho) := LinearMap.toContinuousLinearMap (a k)
  apply for_representation R _ Spin.K
  · apply continuous_iff_continuousAt.mpr; intro k
    exact Dash.fit_plane a (a k) fun x => (h.spin d x).continuousAt
  · ext1 x
    exact h.fixes d x
  · intro k s; ext1 x
    exact h.sends d k s x
  intro i
  exact fit_derivative (fun t => a (Ortho.oneParameter (Spin.K i) t))
    (T.lie d (Spin.K i)) (fun x => h.spinAt d (Spin.K i) x)

end YM.Work.A12
