import Audit.Reduction.Defs

set_option autoImplicit false
noncomputable section
namespace YMAudit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ### Coordinates on `Points n` -/

/-- Real coordinates of an `n`-point configuration. -/
private abbrev Coord (n : ℕ) := Fin n × Axis

/-- Regrouping the coordinates of `EuclideanSpace ℝ (Coord n)` into `n` spacetime points. -/
private def curryLinearEquiv (n : ℕ) : EuclideanSpace ℝ (Coord n) ≃ₗ[ℝ] Points n where
  toFun v := WithLp.toLp 2 (fun i => WithLp.toLp 2 (fun a => v (i, a)))
  invFun x := WithLp.toLp 2 (fun q => x q.1 q.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private lemma norm_curryLinearEquiv (n : ℕ) (v : EuclideanSpace ℝ (Coord n)) :
    ‖curryLinearEquiv n v‖ = ‖v‖ := by
  have h : ‖curryLinearEquiv n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

/-- The regrouping as a linear isometry equivalence. -/
private def curryIso (n : ℕ) : EuclideanSpace ℝ (Coord n) ≃ₗᵢ[ℝ] Points n :=
  { curryLinearEquiv n with norm_map' := norm_curryLinearEquiv n }

/-- The coordinate map `(Coord n → ℝ) → Points n` as a measurable equivalence. -/
private def toPoints (n : ℕ) : (Coord n → ℝ) ≃ᵐ Points n :=
  (MeasurableEquiv.toLp 2 (Coord n → ℝ)).trans (curryIso n).toMeasurableEquiv

private lemma measurePreserving_toPoints (n : ℕ) :
    MeasurePreserving (toPoints n) volume volume :=
  (curryIso n).measurePreserving.comp (PiLp.volume_preserving_toLp (Coord n))

private lemma continuous_toPoints (n : ℕ) : Continuous (toPoints n) :=
  (curryIso n).continuous.comp (PiLp.continuous_toLp 2 _)

/-! ### The half-open box and its lattice points -/

/-- The half-open box `(-P/2, P/2]` in every coordinate. -/
private def halfBox (n : ℕ) (P : ℝ) : Set (Coord n → ℝ) :=
  Set.pi univ fun _ => Ioc (-(P / 2)) (P / 2)

private lemma isBounded_halfBox (n : ℕ) (P : ℝ) : Bornology.IsBounded (halfBox n P) :=
  Bornology.IsBounded.pi fun _ => Metric.isBounded_Ioc _ _

private lemma measurableSet_halfBox (n : ℕ) (P : ℝ) : MeasurableSet (halfBox n P) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

private lemma volume_frontier_halfBox (n : ℕ) (P : ℝ) : volume (frontier (halfBox n P)) = 0 :=
  (convex_pi fun _ _ => convex_Ioc _ _).addHaar_frontier volume

private lemma mesh_pos {g : GaugeGroup} (C : WilsonFamily g) (N : ℕ) : 0 < C.mesh N := by
  unfold WilsonFamily.mesh
  have : (0 : ℝ) < ((C.denominator N).val : ℝ) := by exact_mod_cast (C.denominator N).pos
  positivity

/-- Coordinates of the lattice point indexed by `x`. -/
private def grid {g : GaugeGroup} (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → Site (C.period p * C.denominator N)) : Coord n → ℝ :=
  fun q => C.mesh N * (ZMod.valMinAbs (x q.1 q.2) : ℝ)

private lemma toPoints_grid {g : GaugeGroup} (C : WilsonFamily g) (N p : ℕ) {n : ℕ}
    (x : Fin n → Site (C.period p * C.denominator N)) :
    toPoints n (grid C N p x) = WithLp.toLp 2 fun i => C.place N p (x i) := rfl

private lemma grid_injective {g : GaugeGroup} (C : WilsonFamily g) (N p n : ℕ) :
    Function.Injective (grid C N p (n := n)) := by
  intro x y hxy
  funext i a
  have h := congr_fun hxy (i, a)
  simp only [grid] at h
  have h2 := mul_left_cancel₀ (mesh_pos C N).ne' h
  exact ZMod.valMinAbs_inj.1 (Int.cast_inj.1 h2)

private lemma half_bounds_iff {P D k : ℝ} (hD : 0 < D) :
    (-(P / 2) < D⁻¹ * k ∧ D⁻¹ * k ≤ P / 2) ↔ (-(P * D) < k * 2 ∧ k * 2 ≤ P * D) := by
  rw [inv_mul_eq_div, lt_div_iff₀ hD, div_le_iff₀ hD]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Integer form of the box bounds: `-L < 2k ≤ L` with `L = P * D` iff `k / D ∈ (-P/2, P/2]`. -/
private lemma grid_bounds_iff {L : ℕ} {P D : ℝ} (hD : 0 < D) (hL : (L : ℝ) = P * D) (k : ℤ) :
    k * 2 ∈ Set.Ioc (-(L : ℤ)) L ↔ (-(P / 2) < D⁻¹ * k ∧ D⁻¹ * k ≤ P / 2) := by
  rw [half_bounds_iff hD, Set.mem_Ioc, ← hL]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

open scoped Pointwise in
private lemma range_grid {g : GaugeGroup} (C : WilsonFamily g) (N p n : ℕ) :
    Set.range (grid C N p (n := n)) =
      halfBox n ((C.period p : ℕ) : ℝ) ∩ ((C.denominator N : ℕ) : ℝ)⁻¹ •
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Coord n))) : Set (Coord n → ℝ)) := by
  haveI : NeZero (C.denominator N : ℕ) := ⟨(C.denominator N).ne_zero⟩
  haveI : NeZero (C.period p * C.denominator N).val := ⟨(C.period p * C.denominator N).ne_zero⟩
  have hDpos : (0 : ℝ) < ((C.denominator N : ℕ) : ℝ) := by exact_mod_cast (C.denominator N).pos
  have hmesh : C.mesh N = ((C.denominator N : ℕ) : ℝ)⁻¹ := rfl
  have hL : (((C.period p * C.denominator N).val : ℕ) : ℝ) =
      ((C.period p : ℕ) : ℝ) * ((C.denominator N : ℕ) : ℝ) := by
    push_cast; ring
  ext v
  rw [Set.mem_inter_iff, ← Submodule.coe_pointwise_smul, SetLike.mem_coe,
    BoxIntegral.unitPartition.mem_smul_span_iff]
  simp only [Set.mem_range, halfBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioc]
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨fun q => ?_, fun q => ⟨ZMod.valMinAbs (x q.1 q.2), ?_⟩⟩
    · simp only [grid, hmesh]
      exact (grid_bounds_iff hDpos hL _).1 (ZMod.valMinAbs_mem_Ioc (x q.1 q.2))
    · simp only [grid, hmesh, eq_intCast]
      field_simp
  · rintro ⟨hbox, hlat⟩
    choose k hk using hlat
    refine ⟨fun i a => ((k (i, a) : ℤ) : ZMod (C.period p * C.denominator N).val), ?_⟩
    funext q
    have hv : v q = ((C.denominator N : ℕ) : ℝ)⁻¹ * (k q : ℝ) := by
      rw [← eq_intCast (algebraMap ℤ ℝ), hk q]
      field_simp
    have hval : ZMod.valMinAbs ((k q : ℤ) : ZMod (C.period p * C.denominator N).val) = k q :=
      (ZMod.valMinAbs_spec _ _).2 ⟨rfl, (grid_bounds_iff hDpos hL _).2 (hv ▸ hbox q)⟩
    simp only [grid, hmesh]
    rw [hval, hv]

open scoped Pointwise in
/-- The lattice sum of Mathlib's Riemann-sum theorem is the sum over the sites of the torus. -/
private lemma tsum_grid {g : GaugeGroup} (C : WilsonFamily g) (N p n : ℕ)
    (F : (Coord n → ℝ) → ℝ) :
    ∑' v : ↑(halfBox n ((C.period p : ℕ) : ℝ) ∩ ((C.denominator N : ℕ) : ℝ)⁻¹ •
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Coord n))) : Set (Coord n → ℝ))), F v =
      ∑ x : Fin n → Site (C.period p * C.denominator N), F (grid C N p x) := by
  rw [← range_grid, tsum_range F (grid_injective C N p n), tsum_fintype]

/-! ### Riemann sums -/

/-- Real-valued Riemann sums over the lattice points of the box converge to the integral. -/
private lemma riemann_real {g : GaugeGroup} (C : WilsonFamily g) (p n : ℕ) (F : (Coord n → ℝ) → ℝ)
    (hF : Continuous F) (hvan : ∀ v, v ∉ halfBox n ((C.period p : ℕ) : ℝ) → F v = 0) :
    Tendsto (fun N => C.mesh N ^ (4 * n) *
        ∑ x : Fin n → Site (C.period p * C.denominator N), F (grid C N p x))
      atTop (𝓝 (∫ v, F v)) := by
  have h := (tendsto_tsum_div_pow_atTop_integral (halfBox n ((C.period p : ℕ) : ℝ)) F hF
    (isBounded_halfBox _ _) (measurableSet_halfBox _ _) (volume_frontier_halfBox _ _)).comp
    C.denominatorStrict.tendsto_atTop
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hvan] at h
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [tsum_grid, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  simp only [WilsonFamily.mesh]
  ring

/-- Riemann sums: for any Wilson family and any separated test supported in the open box of
side `period p`, the lattice sums used by `smear` converge to the integral. -/
theorem riemann_tendsto {g : GaugeGroup} (C : WilsonFamily g) (p : ℕ) {n : ℕ}
    (t : WilsonFamily.SeparatedTest n) (ht : C.suitable p t) :
    Tendsto (fun N => (C.mesh N : ℂ) ^ (4 * n) *
        ∑ x : Fin n → Site (C.period p * C.denominator N),
          t (WithLp.toLp 2 fun i => C.place N p (x i)))
      atTop (𝓝 (∫ x, t x)) := by
  have hvan : ∀ v, v ∉ halfBox n ((C.period p : ℕ) : ℝ) → t (toPoints n v) = 0 := by
    intro v hv
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    apply hv
    intro q _
    have h := ht hmem q.1 q.2
    exact ⟨h.1, h.2.le⟩
  have hc : Continuous fun v => t (toPoints n v) := t.continuous.comp (continuous_toPoints n)
  have hre := riemann_real C p n (fun v => (t (toPoints n v)).re) (Complex.continuous_re.comp hc)
    (fun v hv => by simp only [hvan v hv, Complex.zero_re])
  have him := riemann_real C p n (fun v => (t (toPoints n v)).im) (Complex.continuous_im.comp hc)
    (fun v hv => by simp only [hvan v hv, Complex.zero_im])
  have hint : Integrable (fun x : Points n => t x) :=
    t.continuous.integrable_of_hasCompactSupport t.hasCompactSupport
  have hre' : ∫ v, (t (toPoints n v)).re = (∫ x, t x).re := by
    rw [(measurePreserving_toPoints n).integral_comp' (fun x => (t x).re)]
    exact integral_re hint
  have him' : ∫ v, (t (toPoints n v)).im = (∫ x, t x).im := by
    rw [(measurePreserving_toPoints n).integral_comp' (fun x => (t x).im)]
    exact integral_im hint
  rw [hre'] at hre
  rw [him'] at him
  have hsum := ((Complex.continuous_ofReal.tendsto _).comp hre).add
    (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  rw [Complex.re_add_im] at hsum
  refine hsum.congr fun N => ?_
  apply Complex.ext <;> simp [toPoints_grid, Complex.re_sum, Complex.im_sum] <;> ring

end YMAudit
