import ChallengeSpec
import Audit.Reduction.Defs
/-! Audit probe (group: inventory, completeness review of the trusted-definition audit). Not part of the
submission. Part 1 is the verbatim concatenation of the current Audit/Reduction sources (Regular, Haar,
Trace, Law, Riemann, Converges, Recon, OPE, Main; import lines removed), so that `jointExistence_of_continuum`
is re-checked here. Part 2 (namespaces InventoryTransfer, InventorySU2, InventoryAliases) is new.
Part 1 sits in the namespace `YMAudit.CrossgroupProbe` instead of `YMAudit`, so its names do not
collide with the originals in a source index of the whole tree; nothing else in it changed. -/
-- ===== from Audit/Reduction/Regular.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The gauge-blind family satisfies every clause of `WilsonRegularity`. -/
theorem blind_regular {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] :
    WilsonRegularity (blindFamily μ hH F) := by
  refine ⟨⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩,
    fun _ _ _ _ => continuous_const, fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨∅, fun _ _ _ => by intro sites U V _; rfl⟩⟩
  have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
  have hd : (blindFamily μ hH F).beta N p / Real.log ((blindFamily μ hH F).mesh N)⁻¹ = 1 := by
    show Real.log ((N + 2 : ℕ) : ℝ) / Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = 1
    rw [inv_inv, div_self hpos.ne']
  rw [hd, sub_self, abs_zero]
  exact hε

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Haar.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The unitary group of `k × k` complex matrices is a compact subset of the matrices: it is
closed, and every entry of a unitary matrix lies in the closed unit ball of `ℂ`. -/
theorem isCompact_unitaryGroup (k : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  refine (IsCompact.matrix (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
    isClosed_unitary ?_
  intro U hU i j
  simpa using entry_norm_bound_of_unitary hU i j

/-- The image of a gauge group is a compact space (a closed subgroup of the compact unitary
group). -/
theorem compactSpace_image (g : GaugeGroup) : CompactSpace g.image := by
  haveI : CompactSpace (UnitaryRepresentation g.n) :=
    isCompact_iff_compactSpace.mp (isCompact_unitaryGroup (g.n + 1))
  exact isCompact_iff_compactSpace.mp g.imageClosed.isCompact

/-- Every gauge group carries a Haar probability measure (for the Borel structure declared
in `PublicWilson`). -/
theorem exists_haar (g : GaugeGroup) :
    ∃ μ : Measure g.image, IsProbabilityMeasure μ ∧ μ.IsHaarMeasure := by
  haveI := compactSpace_image g
  refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  have h := Measure.haarMeasure_self (G := g.image) (K₀ := ⊤)
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Trace.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The trace test only reads the selected phase, which is `T₀`'s selected phase. -/
theorem reduced_trace {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hT : T₀.TraceTest) : (reduced T₀ μ hH).TraceTest := by
  have htwo : (reduced T₀ μ hH).traceTwo = T₀.traceTwo := by
    funext r
    simp only [Hierarchy.traceTwo, reduced, redCorrelation, ↓reduceIte]
  refine ⟨fun f => hT.centered f, hT.amplitudePositive, ?_, ?_⟩
  · rw [htwo]; exact hT.shortDistance
  · intro terms; rw [htwo]; exact hT.excludes terms

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Law.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- Square complex matrices form a second-countable space (`Matrix` is a type synonym for
`Fin k → Fin k → ℂ`, but instance search does not see through it). -/
theorem matrix_secondCountable (k : ℕ) : SecondCountableTopology (Matrix (Fin k) (Fin k) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin k → Fin k → ℂ))

/-- The unitary group carries the subspace topology of the matrices, so it is second countable. -/
theorem unitary_secondCountable (k : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin k) ℂ) := by
  haveI := matrix_secondCountable k
  exact TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-- The gauge group carries the subspace topology of the unitary group. -/
theorem image_secondCountable (g : GaugeGroup) : SecondCountableTopology g.image := by
  haveI := unitary_secondCountable (g.n + 1)
  exact TopologicalSpace.secondCountableTopology_induced _ _ Subtype.val

/-- The Wilson energy is a continuous function of the configuration. -/
theorem wilsonEnergy_continuous (g : GaugeGroup) (l : ℕ+) :
    Continuous (fun U : Configuration g l => wilsonEnergy U) := by
  unfold wilsonEnergy
  refine continuous_finsetSum _ (fun p _ => ?_)
  refine continuous_const.sub ((Complex.continuous_re.comp ?_).div_const _)
  refine Continuous.matrix_trace ?_
  refine continuous_subtype_val.comp (continuous_subtype_val.comp ?_)
  unfold plaquette
  fun_prop

/-- The real part of the trace of a gauge-group element is bounded by the matrix size. -/
theorem abs_re_trace_le (g : GaugeGroup) (P : g.image) :
    |(P.val.val.trace).re| ≤ ((g.n + 1 : ℕ) : ℝ) := by
  have hmem : P.val.val ∈ Matrix.unitaryGroup (Fin (g.n + 1)) ℂ := P.val.prop
  calc |(P.val.val.trace).re| ≤ ‖P.val.val.trace‖ := Complex.abs_re_le_norm _
    _ = ‖∑ i, P.val.val i i‖ := rfl
    _ ≤ ∑ i, ‖P.val.val i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (g.n + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hmem i i
    _ = ((g.n + 1 : ℕ) : ℝ) := by simp

/-- Each plaquette term of the Wilson energy lies in `[-2, 2]`. -/
theorem abs_plaquetteTerm_le (g : GaugeGroup) (P : g.image) :
    |1 - (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ)| ≤ 2 := by
  have h1 := abs_re_trace_le g P
  have hpos : (0 : ℝ) < ((g.n + 1 : ℕ) : ℝ) := by positivity
  rw [abs_le] at h1 ⊢
  have hle : (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) ≤ 1 := (div_le_one hpos).mpr h1.2
  have hge : -1 ≤ (P.val.val.trace).re / ((g.n + 1 : ℕ) : ℝ) := by
    rw [le_div_iff₀ hpos]; linarith
  constructor <;> linarith

/-- The Wilson energy is uniformly bounded. -/
theorem abs_wilsonEnergy_le (g : GaugeGroup) (l : ℕ+) (U : Configuration g l) :
    |wilsonEnergy U| ≤ ∑ _p : Site l × Directions, (2 : ℝ) := by
  unfold wilsonEnergy
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun p _ => abs_plaquetteTerm_le g _)

/-- The unnormalized Wilson weight is uniformly bounded. -/
theorem wilsonWeight_le (g : GaugeGroup) (l : ℕ+) (β : ℝ) (U : Configuration g l) :
    ‖Real.exp (-β * wilsonEnergy U)‖ ≤ Real.exp (|β| * ∑ _p : Site l × Directions, (2 : ℝ)) := by
  have hle : -β * wilsonEnergy U ≤ |β| * ∑ _p : Site l × Directions, (2 : ℝ) :=
    calc -β * wilsonEnergy U ≤ |-β * wilsonEnergy U| := le_abs_self _
      _ = |β| * |wilsonEnergy U| := by rw [abs_mul, abs_neg]
      _ ≤ |β| * ∑ _p : Site l × Directions, (2 : ℝ) :=
          mul_le_mul_of_nonneg_left (abs_wilsonEnergy_le g l U) (abs_nonneg β)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr hle

/-- The unnormalized Wilson weight is integrable against the product Haar prior. -/
theorem wilsonWeight_integrable (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] :
    Integrable (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U))
      (Measure.pi fun _ => μ) := by
  haveI := image_secondCountable g
  have hcont : Continuous (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U)) :=
    Real.continuous_exp.comp (continuous_const.mul (wilsonEnergy_continuous g l))
  exact Integrable.of_bound hcont.aestronglyMeasurable _
    (ae_of_all _ fun U => wilsonWeight_le g l β U)

/-- The normalized Wilson law is a probability measure. -/
theorem wilsonLaw_isProbability (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (wilsonLaw g l β μ) := by
  have h := isProbabilityMeasure_tilted (μ := Measure.pi fun _ : Site l × Axis => μ)
    (f := fun U => -β * wilsonEnergy U) (wilsonWeight_integrable g l β μ)
  exact h

/-- Finite moments of the gauge-blind family are the indicator `allZero`. -/
theorem blind_finiteMoment {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] (N p : ℕ) {n : ℕ}
    (v : Fin n → Σ d, F d)
    (x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N)) :
    (blindFamily μ hH F).finiteMoment N p v x = allZero v := by
  haveI := (blindFamily μ hH F).probability
  haveI := wilsonLaw_isProbability g ((blindFamily μ hH F).period p *
    (blindFamily μ hH F).denominator N) ((blindFamily μ hH F).beta N p) (blindFamily μ hH F).haar
  have hconst : ∀ U, (∏ i, (blindFamily μ hH F).insertion N p (v i) (x i) U) = allZero v := by
    intro U
    classical
    show (∏ i, (if v i = zeroTag F then (1 : ℂ) else 0)) = allZero v
    unfold allZero
    by_cases h : ∀ i, v i = zeroTag F
    · rw [if_pos h]
      exact Finset.prod_eq_one (fun i _ => if_pos (h i))
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  unfold WilsonFamily.finiteMoment
  simp only [hconst, integral_const, probReal_univ, one_smul]

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Riemann.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
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

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Converges.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-- A compactly supported test eventually fits in the box of every large volume. -/
theorem eventually_suitable {g : GaugeGroup} (C : WilsonFamily g) {order : ℕ → ℕ}
    (ho : StrictMono order) {n : ℕ} (t : WilsonFamily.SeparatedTest n) :
    ∀ᶠ k in atTop, C.suitable (order k) t := by
  have hK : IsCompact (tsupport t) := t.hasCompactSupport
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  refine Filter.eventually_atTop.2 ⟨⌈2 * R⌉₊ + 1, fun k hk => ?_⟩
  intro x hx i a
  have h1 : |x i a| ≤ R :=
    calc |x i a| = ‖x i a‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x i‖ := PiLp.norm_apply_le (x i) a
      _ ≤ ‖x‖ := PiLp.norm_apply_le x i
      _ ≤ R := hR x hx
  have h2 : (k : ℝ) ≤ ((C.period (order k)).val : ℝ) := by
    have hk1 : k ≤ order k := ho.le_apply
    have hk2 : order k ≤ (C.period (order k)).val := C.periodStrict.le_apply
    exact_mod_cast hk1.trans hk2
  have h3 : 2 * R < k := by
    have hc := Nat.le_ceil (2 * R)
    have hk' : ((⌈2 * R⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at hk'
    linarith
  have h4 := neg_abs_le (x i a)
  have h5 := le_abs_self (x i a)
  constructor <;> linarith

/-- The gauge-blind family converges, along any strictly increasing volume order, to the
indicator `allZero`, given the moment identity and the Riemann-sum limit. -/
theorem blind_converges {g : GaugeGroup} (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (F : ℕ → Type) [∀ d, Zero (F d)] {order : ℕ → ℕ}
    (ho : StrictMono order)
    (hmoment : ∀ (N p : ℕ) {n : ℕ} (v : Fin n → Σ d, F d)
      (x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N)),
      (blindFamily μ hH F).finiteMoment N p v x = allZero v)
    (hriemann : ∀ (p : ℕ) {n : ℕ} (t : WilsonFamily.SeparatedTest n),
      (blindFamily μ hH F).suitable p t →
      Tendsto (fun N => ((blindFamily μ hH F).mesh N : ℂ) ^ (4 * n) *
          ∑ x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N),
            t (WithLp.toLp 2 fun i => (blindFamily μ hH F).place N p (x i)))
        atTop (𝓝 (∫ x, t x))) :
    (blindFamily μ hH F).Converges order (fun v _ => allZero v) := by
  intro n v t
  refine ⟨eventually_suitable _ ho t, fun _ => (∫ x, t x) * allZero v, fun p hp => ?_, ?_⟩
  · have key : ∀ N, (blindFamily μ hH F).smear N p v t =
        (((blindFamily μ hH F).mesh N : ℂ) ^ (4 * n) *
          ∑ x : Fin n → Site ((blindFamily μ hH F).period p * (blindFamily μ hH F).denominator N),
            t (WithLp.toLp 2 fun i => (blindFamily μ hH F).place N p (x i))) * allZero v := by
      intro N
      simp only [WilsonFamily.smear, hmoment, Finset.sum_mul, mul_assoc]
    simp only [key]
    exact (hriemann p t hp).mul_const _
  · simp only [integral_mul_const]
    exact tendsto_const_nhds

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Recon.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

section ReconHelpers

open scoped ContDiff

/-- `allZero` is invariant under reindexing by an equivalence. -/
private theorem allZero_comp_equiv {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (w : ι → Σ d, F d) (e : κ ≃ ι) : allZero (w ∘ e) = allZero w := by
  unfold allZero
  by_cases h : ∀ i, w i = zeroTag F
  · rw [if_pos h]
    exact if_pos (fun k => h (e k))
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    intro i
    simpa using h' (e.symm i)

/-- The two phases are distinct. -/
private theorem phase1_ne_phase0 : phase1 ≠ phase0 := by
  intro h
  have h' := congrArg Subtype.val h
  simp [phase0, phase1] at h'

/-- Every phase is `phase0` or `phase1`. -/
private theorem phase_cases (p : Phase) : p = phase0 ∨ p = phase1 := by
  obtain ⟨v, hv⟩ := p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with rfl | rfl
  · left; rfl
  · right; rfl

/-- The uniform measure on the two phases is a probability measure. -/
private theorem phaseMeasure_isProbability : IsProbabilityMeasure phaseMeasure := by
  constructor
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
  rw [one_add_one_eq_two]
  exact ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top

/-- The uniform measure on the two phases charges every nonempty open set. -/
private theorem phaseMeasure_isOpenPos : phaseMeasure.IsOpenPosMeasure := by
  refine ⟨fun U _ hne => ?_⟩
  obtain ⟨p, hp⟩ := hne
  simp only [phaseMeasure, Measure.smul_apply, Measure.add_apply, smul_eq_mul]
  refine mul_ne_zero (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) ?_
  rcases phase_cases p with rfl | rfl
  · rw [Measure.dirac_apply_of_mem hp]
    simp
  · rw [Measure.dirac_apply_of_mem hp]
    simp

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

private theorem redCorrelation_none {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    redCorrelation T₀ none w x = allZero w := rfl

private theorem redCorrelation_phase0 {n : ℕ} (w : Fin n → T₀.Tag) (x : Points n) :
    redCorrelation T₀ (some phase0) w x = T₀.correlation (some T₀.selected) w x := by
  simp only [redCorrelation, ↓reduceIte]

private theorem redCorrelation_of_ne {n : ℕ} {i : Phase} (hi : i ≠ phase0) (w : Fin n → T₀.Tag)
    (x : Points n) :
    redCorrelation T₀ (some i) w x = 2 * allZero w - T₀.correlation (some T₀.selected) w x := by
  simp only [redCorrelation]
  exact if_neg hi

private theorem redCorrelation_perm (hR : T₀.Reconstructed) (s : Option Phase) {n : ℕ}
    (a : Fin n → T₀.Tag) (x : Points n) (hx : x ∈ WilsonFamily.separated n)
    (π : Equiv.Perm (Fin n)) :
    redCorrelation T₀ s (a ∘ π) (WithLp.toLp 2 (x.ofLp ∘ π)) = redCorrelation T₀ s a x := by
  have hA : allZero (a ∘ π) = allZero a := allZero_comp_equiv a π
  have hS := hR.permutation (some T₀.selected) a x hx π
  cases s with
  | none => exact hA
  | some i =>
    by_cases hi : i = phase0
    · subst hi
      rw [redCorrelation_phase0, redCorrelation_phase0, hS]
    · rw [redCorrelation_of_ne T₀ hi, redCorrelation_of_ne T₀ hi, hS, hA]

private theorem redCorrelation_smooth (hR : T₀.Reconstructed) (s : Option Phase) {n : ℕ}
    (a : Fin n → T₀.Tag) :
    ContDiffOn ℝ ∞ (redCorrelation T₀ s a) (WilsonFamily.separated n) := by
  cases s with
  | none =>
    have h : redCorrelation T₀ none a = fun _ => allZero a := by
      funext x
      exact redCorrelation_none T₀ a x
    rw [h]
    exact contDiffOn_const
  | some i =>
    by_cases hi : i = phase0
    · have h : redCorrelation T₀ (some i) a = T₀.correlation (some T₀.selected) a := by
        funext x
        subst hi
        exact redCorrelation_phase0 T₀ a x
      rw [h]
      exact hR.smooth (some T₀.selected) a
    · have h : redCorrelation T₀ (some i) a =
          fun x => 2 * allZero a - T₀.correlation (some T₀.selected) a x := by
        funext x
        exact redCorrelation_of_ne T₀ hi a x
      rw [h]
      exact contDiffOn_const.sub (hR.smooth (some T₀.selected) a)

private theorem redCorrelation_continuous {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    Continuous (fun i : Phase => redCorrelation T₀ (some i) a x) :=
  continuous_of_discreteTopology

private theorem redCorrelation_mixture {n : ℕ} (a : Fin n → T₀.Tag) (x : Points n) :
    (∫ i, redCorrelation T₀ (some i) a x ∂phaseMeasure) = redCorrelation T₀ none a x := by
  have hi0 : Integrable (fun i : Phase => redCorrelation T₀ (some i) a x)
      (Measure.dirac phase0) := Integrable.of_finite
  have hi1 : Integrable (fun i : Phase => redCorrelation T₀ (some i) a x)
      (Measure.dirac phase1) := Integrable.of_finite
  rw [phaseMeasure, integral_smul_measure, integral_add_measure hi0 hi1, integral_dirac,
    integral_dirac, redCorrelation_phase0, redCorrelation_of_ne T₀ phase1_ne_phase0,
    redCorrelation_none, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul]
  push_cast
  ring

end ReconHelpers

/-- The reduced hierarchy satisfies `Reconstructed`: the selected-phase clauses are `T₀`'s,
and the two phases average to the Wilson limit `allZero`. -/
theorem reduced_reconstructed {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hR : T₀.Reconstructed) : (reduced T₀ μ hH).Reconstructed := by
  exact
    { axioms := hR.axioms
      faithful := hR.faithful
      injective := hR.injective
      acts := hR.acts
      covers := hR.covers
      represents := Function.surjective_id
      normalized := phaseMeasure_isProbability
      fullSupport := phaseMeasure_isOpenPos
      permutation := fun s _ a x hx π => redCorrelation_perm T₀ hR s a x hx π
      smooth := fun s _ a => redCorrelation_smooth T₀ hR s a
      characterContinuity := fun a x _ => redCorrelation_continuous T₀ a x
      mixture := fun a x _ => redCorrelation_mixture T₀ a x
      analytic := hR.analytic
      root := fun v x h => (hR.root v x h).trans (redCorrelation_phase0 T₀ v x).symm
      boundary := hR.boundary }

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/OPE.lean =====

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

section OPEHelpers

/- `Hierarchy.grouped` is elaborated under `open scoped Classical` (its `Fintype.equivFin`
needs `DecidableEq`); we open it too so that our restatement below uses the same instances. -/
open scoped Classical

/-! ### Bookkeeping for `allZero` -/

/-- `allZero` is invariant under reindexing by an equivalence. -/
private theorem ope_allZero_comp_equiv {F : ℕ → Type} [∀ d, Zero (F d)] {ι κ : Type}
    (w : ι → Σ d, F d) (e : κ ≃ ι) : allZero (w ∘ e) = allZero w := by
  unfold allZero
  by_cases h : ∀ i, w i = zeroTag F
  · rw [if_pos h]
    exact if_pos (fun k => h (e k))
  · rw [if_neg h, if_neg]
    intro h'
    apply h
    intro i
    simpa using h' (e.symm i)

/-- `allZero` of a concatenated word is the product. -/
private theorem ope_allZero_sumElim {F : ℕ → Type} [∀ d, Zero (F d)] {I J : Type}
    (a : I → Σ d, F d) (b : J → Σ d, F d) :
    allZero (Sum.elim a b) = allZero a * allZero b := by
  unfold allZero
  by_cases ha : ∀ i, a i = zeroTag F
  · by_cases hb : ∀ j, b j = zeroTag F
    · have hab : ∀ k, Sum.elim a b k = zeroTag F := fun k => by
        cases k with
        | inl i => exact ha i
        | inr j => exact hb j
      rw [if_pos ha, if_pos hb, if_pos hab, mul_one]
    · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => hb fun j => h (Sum.inr j)
      rw [if_neg hb, if_neg hab, mul_zero]
  · have hab : ¬ ∀ k, Sum.elim a b k = zeroTag F := fun h => ha fun i => h (Sum.inl i)
    rw [if_neg ha, if_neg hab, zero_mul]

private theorem ope_allZero_unit_of_eq {F : ℕ → Type} [∀ d, Zero (F d)] {t : Σ d, F d}
    (h : t = zeroTag F) : allZero (fun _ : Unit => t) = 1 := by
  unfold allZero
  exact if_pos fun _ => h

private theorem ope_allZero_unit_of_ne {F : ℕ → Type} [∀ d, Zero (F d)] {t : Σ d, F d}
    (h : ¬ t = zeroTag F) : allZero (fun _ : Unit => t) = 0 := by
  unfold allZero
  exact if_neg fun h' => h (h' ())

private theorem ope_norm_allZero_le {F : ℕ → Type} [∀ d, Zero (F d)] {ι : Type}
    (w : ι → Σ d, F d) : ‖allZero w‖ ≤ 1 := by
  unfold allZero
  split_ifs <;> simp

/-- The double sum `∑ ∑ c (2N - Z)` splits linearly. -/
private theorem ope_sum_sum_two_mul_sub {α : Type} [Fintype α] {β : α → Type}
    [∀ k, Fintype (β k)] (c N Z : (k : α) → β k → ℂ) :
    ∑ k, ∑ i, c k i * (2 * N k i - Z k i) =
      2 * ∑ k, ∑ i, c k i * N k i - ∑ k, ∑ i, c k i * Z k i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)

private theorem ope_weight_nonneg {I : Type} [Fintype I] (a : I → T₀.Tag) :
    0 ≤ T₀.weight a :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-! ### Coefficients -/

private theorem ope_coeff_none_zero {I : Type} [Fintype I] (a : I → T₀.Tag)
    (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a 0 none x o = allZero a := by
  simp only [redCoefficient, ↓reduceIte]

private theorem ope_coeff_none_ne {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    (hj : j ≠ 0) (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a j none x o = 0 :=
  if_neg hj

private theorem ope_coeff_some_of_eq {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    {i : T₀.Channel j} (h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) : redCoefficient T₀ a j (some i) x o = 0 :=
  if_pos h

private theorem ope_coeff_some_of_ne {I : Type} [Fintype I] (a : I → T₀.Tag) {j : ℕ}
    {i : T₀.Channel j} (h : ¬ (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field)
    (x : I → Spacetime) (o : Spacetime) :
    redCoefficient T₀ a j (some i) x o = T₀.coefficient a j i x o :=
  if_neg h

/-- The coefficient bound for the reduced channels. -/
private theorem ope_coeff_bound (hO : T₀.OperatorProductExpansion) {I : Type} [Fintype I]
    (a : I → T₀.Tag) (M η ε : ℝ) (hM : 0 ≤ M) (hη : 0 < η) (hε : 0 < ε) (j : ℕ)
    (i : Option (T₀.Channel j)) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x o, Hierarchy.Within r M η x o →
      ‖redCoefficient T₀ a j i x o‖ ≤ r ^ ((j:ℝ) - T₀.weight a - ε) := by
  rcases i with _ | i
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0:ℝ) < 1)] with r hr x o _
    by_cases hj : j = 0
    · subst hj
      rw [ope_coeff_none_zero]
      refine (ope_norm_allZero_le a).trans
        (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr.1 hr.2.le ?_)
      have := ope_weight_nonneg T₀ a
      push_cast
      linarith
    · rw [ope_coeff_none_ne T₀ a hj, norm_zero]
      exact Real.rpow_nonneg hr.1.le _
  · filter_upwards [hO.coefficients a M η ε hM hη hε j i, self_mem_nhdsWithin]
      with r hr hr0
    intro x o hW
    by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
    · rw [ope_coeff_some_of_eq T₀ a h, norm_zero]
      exact Real.rpow_nonneg (Set.mem_Ioi.mp hr0).le _
    · rw [ope_coeff_some_of_ne T₀ a h]
      exact hr x o hW

/-! ### Grouped correlations of the reduced hierarchy, written with `T₀`'s data -/

/-- `redCorrelation` on the grouped configuration of `(a, x)` and `(b, y)`; this is
definitionally `(reduced T₀ μ hH).grouped s a x b y`. -/
private def opeGrouped (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) : ℂ :=
  redCorrelation T₀ s (Sum.elim a b ∘ (Fintype.equivFin (I ⊕ J)).symm)
    (WithLp.toLp 2 (Sum.elim x y ∘ (Fintype.equivFin (I ⊕ J)).symm))

/-- The OPE remainder of the reduced hierarchy at phase `s`, written with `T₀`'s data. -/
private def opeRem (s : Option Phase) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) : ℂ :=
  opeGrouped T₀ s a x b y - ∑ j : Fin (D+1), ∑ i : Option (T₀.Channel j.val),
    redCoefficient T₀ a j.val i x o *
      opeGrouped T₀ s (fun _ : Unit => (⟨j.val, redActor T₀ j.val i⟩ : T₀.Tag)) (fun _ => o) b y

private theorem opeGrouped_none {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ none a x b y = allZero a * allZero b := by
  unfold opeGrouped
  simp only [redCorrelation]
  rw [ope_allZero_comp_equiv, ope_allZero_sumElim]

private theorem opeGrouped_phase0 {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ (some phase0) a x b y = T₀.grouped (some T₀.selected) a x b y := by
  unfold opeGrouped
  simp only [redCorrelation, ↓reduceIte]
  rfl

private theorem opeGrouped_other {p : Phase} (hp : p ≠ phase0) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) :
    opeGrouped T₀ (some p) a x b y =
      2 * opeGrouped T₀ none a x b y - opeGrouped T₀ (some phase0) a x b y := by
  unfold opeGrouped
  simp only [redCorrelation, if_neg hp, ↓reduceIte]

/-- A word containing the zero tag exists for any enumeration of `Unit ⊕ J`. -/
private theorem ope_exists_zero {J : Type} {n : ℕ} (σ : Fin n ≃ Unit ⊕ J) {t : T₀.Tag}
    (ht : t = zeroTag T₀.Field) (b : J → T₀.Tag) :
    ∃ i, (Sum.elim (fun _ : Unit => t) b ∘ σ) i = zeroTag T₀.Field :=
  ⟨σ.symm (Sum.inl ()), by simp [ht]⟩

/-- In `T₀`'s selected phase, a grouped word whose actor slot is the zero tag vanishes. -/
private theorem ope_grouped_unit_zero (hZ : ZeroInvisible T₀) {J : Type} [Fintype J]
    {t : T₀.Tag} (ht : t = zeroTag T₀.Field) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) :
    T₀.grouped (some T₀.selected) (fun _ : Unit => t) (fun _ => o) b y = 0 :=
  hZ _ _ _ (ope_exists_zero T₀ _ ht b)

/-! ### Inner sums over the channels `Option (T₀.Channel j)` -/

private theorem ope_inner_none {I : Type} [Fintype I] (a : I → T₀.Tag) (x : I → Spacetime)
    (o : Spacetime) (B : ℂ) (j : ℕ) :
    ∑ i : Option (T₀.Channel j), redCoefficient T₀ a j i x o *
        (allZero (fun _ : Unit => (⟨j, redActor T₀ j i⟩ : T₀.Tag)) * B) =
      if j = 0 then allZero a * B else 0 := by
  have hnone : redCoefficient T₀ a j none x o *
      (allZero (fun _ : Unit => (⟨j, redActor T₀ j none⟩ : T₀.Tag)) * B) =
      if j = 0 then allZero a * B else 0 := by
    by_cases hj : j = 0
    · subst hj
      rw [if_pos rfl, ope_coeff_none_zero,
        ope_allZero_unit_of_eq
          (show (⟨0, redActor T₀ 0 none⟩ : T₀.Tag) = zeroTag T₀.Field from rfl),
        one_mul]
    · rw [if_neg hj, ope_coeff_none_ne T₀ a hj, zero_mul]
  rw [Fintype.sum_option, hnone, Finset.sum_eq_zero, add_zero]
  intro i _
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · rw [ope_coeff_some_of_eq T₀ a h, zero_mul]
  · rw [ope_allZero_unit_of_ne
      (show ¬ (⟨j, redActor T₀ j (some i)⟩ : T₀.Tag) = zeroTag T₀.Field from h),
      zero_mul, mul_zero]

private theorem ope_inner_phase0 (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (j : ℕ) :
    ∑ i : Option (T₀.Channel j), redCoefficient T₀ a j i x o *
        T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, redActor T₀ j i⟩ : T₀.Tag))
          (fun _ => o) b y =
      ∑ i : T₀.Channel j, T₀.coefficient a j i x o *
        T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, T₀.actor j i⟩ : T₀.Tag))
          (fun _ => o) b y := by
  have hnone : redCoefficient T₀ a j none x o *
      T₀.grouped (some T₀.selected) (fun _ : Unit => (⟨j, redActor T₀ j none⟩ : T₀.Tag))
        (fun _ => o) b y = 0 := by
    by_cases hj : j = 0
    · subst hj
      rw [ope_grouped_unit_zero T₀ hZ
        (show (⟨0, redActor T₀ 0 none⟩ : T₀.Tag) = zeroTag T₀.Field from rfl), mul_zero]
    · rw [ope_coeff_none_ne T₀ a hj, zero_mul]
  rw [Fintype.sum_option, hnone, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : (⟨j, T₀.actor j i⟩ : T₀.Tag) = zeroTag T₀.Field
  · rw [ope_coeff_some_of_eq T₀ a h, zero_mul, ope_grouped_unit_zero T₀ hZ h, mul_zero]
  · rw [ope_coeff_some_of_ne T₀ a h]
    rfl

/-! ### The three phases -/

private theorem opeRem_none {I J : Type} [Fintype I] [Fintype J] (a : I → T₀.Tag)
    (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag) (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ none a x o b y D = 0 := by
  unfold opeRem
  simp only [opeGrouped_none, ope_inner_none]
  rw [Fin.sum_univ_succ]
  simp

private theorem opeRem_phase0 (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ (some phase0) a x o b y D =
      T₀.grouped (some T₀.selected) a x b y - ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val,
        T₀.coefficient a j.val i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => ⟨j.val, T₀.actor j.val i⟩)
            (fun _ => o) b y := by
  unfold opeRem
  simp only [opeGrouped_phase0, ope_inner_phase0 T₀ hZ]

private theorem opeRem_other {p : Phase} (hp : p ≠ phase0) {I J : Type} [Fintype I]
    [Fintype J] (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) :
    opeRem T₀ (some p) a x o b y D =
      2 * opeRem T₀ none a x o b y D - opeRem T₀ (some phase0) a x o b y D := by
  unfold opeRem
  simp only [opeGrouped_other T₀ hp]
  rw [ope_sum_sum_two_mul_sub]
  ring

/-- Every phase of the reduced remainder is bounded by `T₀`'s selected-phase remainder. -/
private theorem opeRem_bound (hZ : ZeroInvisible T₀) {I J : Type} [Fintype I] [Fintype J]
    (a : I → T₀.Tag) (x : I → Spacetime) (o : Spacetime) (b : J → T₀.Tag)
    (y : J → Spacetime) (D : ℕ) (s : Option Phase) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ‖T₀.grouped (some T₀.selected) a x b y - ∑ j : Fin (D+1), ∑ i : T₀.Channel j.val,
        T₀.coefficient a j.val i x o *
          T₀.grouped (some T₀.selected) (fun _ : Unit => ⟨j.val, T₀.actor j.val i⟩)
            (fun _ => o) b y‖ ≤ B) :
    ‖opeRem T₀ s a x o b y D‖ ≤ B := by
  rcases s with _ | p
  · rw [opeRem_none, norm_zero]
    exact hB0
  · by_cases hp : p = phase0
    · subst hp
      rw [opeRem_phase0 T₀ hZ]
      exact hB
    · rw [opeRem_other T₀ hp, opeRem_none, opeRem_phase0 T₀ hZ, mul_zero, zero_sub, norm_neg]
      exact hB

end OPEHelpers

/-- The reduced hierarchy has an all-orders OPE with shared coefficients in every phase. -/
theorem reduced_ope {g : GaugeGroup} {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure)
    (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀) :
    (reduced T₀ μ hH).OperatorProductExpansion := by
  refine ⟨?_, ?_⟩
  · intro I _ a M η ε hM hη hε j i
    exact ope_coeff_bound T₀ hO a M η ε hM hη hε j i
  · intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [hO.remainder a b M η c ε hM hη hc hε D, self_mem_nhdsWithin]
      with r hr hr0
    intro x o y hW hC s
    exact opeRem_bound T₀ hZ a x o b y D s (Real.rpow_nonneg (Set.mem_Ioi.mp hr0).le _)
      (hr x o y hW hC (some T₀.selected))

end YMAudit.CrossgroupProbe

-- ===== from Audit/Reduction/Main.lean =====

/-!
# The lattice clause of the public challenge is redundant

`wilson_clause_redundant`: any hierarchy, over any Wilson family, that satisfies the three
continuum clauses of `Hierarchy.Properties` (and gives correlation `0` to words containing the
zero vector in its selected phase) yields the full per-group statement of `JointExistence`
with a Wilson family whose insertions never read the gauge field.
-/

set_option autoImplicit false
noncomputable section
namespace YMAudit.CrossgroupProbe
open YangMills MeasureTheory Filter Topology Set

theorem wilson_clause_redundant (g : GaugeGroup) {C₀ : WilsonFamily g} (T₀ : Hierarchy C₀)
    (hR : T₀.Reconstructed) (hO : T₀.OperatorProductExpansion) (hT : T₀.TraceTest)
    (hZ : ZeroInvisible T₀) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
      ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) := by
  obtain ⟨μ, hμ, hH⟩ := exists_haar g
  refine ⟨blindFamily μ hH T₀.Field, blind_regular μ hH T₀.Field, fun p hp =>
    ⟨id, strictMono_id, reduced T₀ μ hH, ?_, reduced_reconstructed T₀ μ hH hR,
      reduced_ope T₀ μ hH hO hZ, reduced_trace T₀ μ hH hT⟩⟩
  exact blind_converges μ hH T₀.Field (hp.comp strictMono_id)
    (fun N p' _ v x => blind_finiteMoment μ hH T₀.Field N p' v x)
    (fun p' _ t ht => riemann_tendsto _ p' t ht)

/-- `JointExistence` follows from continuum data alone: no lattice content is needed. -/
theorem jointExistence_of_continuum
    (h : ∀ g : GaugeGroup, g.IsSimple → ∃ (C₀ : WilsonFamily g) (T₀ : Hierarchy C₀),
      T₀.Reconstructed ∧ T₀.OperatorProductExpansion ∧ T₀.TraceTest ∧ ZeroInvisible T₀) :
    JointExistence := by
  intro g hg
  obtain ⟨C₀, T₀, hR, hO, hT, hZ⟩ := h g hg
  exact wilson_clause_redundant g T₀ hR hO hT hZ

end YMAudit.CrossgroupProbe


-- ===== New material: inventory / cross-group transfer (audit probe, not part of the submission) =====

set_option autoImplicit false
noncomputable section

namespace InventoryTransfer
open YangMills YMAudit YMAudit.CrossgroupProbe MeasureTheory Filter Topology Set

/-! ### A. Multilinearity of the Wightman vacuum expectation in the labels -/

theorem inv_vector_smul {H : HilbertSpace} {Labels : FieldLabels} (F : FieldSystem H Labels)
    (k : ℂ) : ∀ w : List (Labels.carrier × TestFunction),
      F.vector (w.map fun p => (k • p.1, p.2)) = k ^ w.length • F.vector w
  | [] => by simp [FieldSystem.vector]
  | p :: w => by
      simp only [List.map_cons, FieldSystem.vector, inv_vector_smul F k w, map_smul,
        LinearMap.smul_apply, smul_smul, List.length_cons]
      first
      | (rw [pow_succ]; done)
      | (rw [pow_succ']; done)
      | (rw [pow_succ, mul_comm]; done)
      | (congr 1; ring)

theorem inv_vacuumExpectation_smul {H : HilbertSpace} {Labels : FieldLabels}
    (F : FieldSystem H Labels) (k : ℂ) {n : ℕ} (l : Fin n → Labels.carrier)
    (t : Fin n → TestFunction) :
    F.vacuumExpectation (fun i => k • l i) t = k ^ n * F.vacuumExpectation l t := by
  have hw : List.ofFn (fun i => (k • l i, t i)) =
      (List.ofFn fun i => (l i, t i)).map (fun p => (k • p.1, p.2)) := by
    rw [List.map_ofFn]; rfl
  simp only [FieldSystem.vacuumExpectation]
  rw [hw, inv_vector_smul, List.length_ofFn, Submodule.coe_smul, inner_smul_right]

/-! ### B. Retarget a hierarchy to any Wilson family and rescale every field label by `k` -/

section Transfer
variable {g₀ : GaugeGroup} {C₀ : WilsonFamily g₀}

/-- Keep every continuum datum of `T`, move it over the Wilson family `C` (of ANY gauge group)
through the token map `proj`, and multiply every field label by `k`.  Then `n`-point
correlations and continuations acquire `k ^ n`, and the OPE coefficients of an `I`-cluster
acquire `k ^ |I| / k`. The Wightman theory itself is unchanged. -/
def transfer (T : Hierarchy C₀) {g : GaugeGroup} (C : WilsonFamily g) (proj : C.Token → T.Tag)
    (k : ℂ) : Hierarchy C where
  H := T.H
  labels := T.labels
  theory := T.theory
  Field := T.Field
  toLabel d := k • T.toLabel d
  project := proj
  Character := T.Character
  phaseMeasure := T.phaseMeasure
  selected := T.selected
  correlation := fun {n} s a x => k ^ n * T.correlation s a x
  continuation := fun {n} v z w => k ^ n * T.continuation v z w
  Channel := T.Channel
  actor := T.actor
  coefficient := fun {I} [Fintype I] a j i x o =>
    k ^ Fintype.card I * k⁻¹ * T.coefficient a j i x o
  centeredTrace := T.centeredTrace

variable (T : Hierarchy C₀) {g : GaugeGroup} (C : WilsonFamily g) (proj : C.Token → T.Tag)
  (k : ℂ)

theorem transfer_grouped {I J : Type} [Fintype I] [Fintype J]
    (s : Option (transfer T C proj k).Character) (a : I → (transfer T C proj k).Tag)
    (x : I → Spacetime) (b : J → (transfer T C proj k).Tag) (y : J → Spacetime) :
    (transfer T C proj k).grouped s a x b y =
      k ^ (Fintype.card I + Fintype.card J) * T.grouped s a x b y := by
  first
  | (rw [← Fintype.card_sum]; rfl)
  | (simp only [Hierarchy.grouped, transfer, Fintype.card_sum])

theorem transfer_traceTwo (r : ℝ) :
    (transfer T C proj k).traceTwo r = k ^ 2 * T.traceTwo r := rfl

theorem transfer_reconstructed (hR : T.Reconstructed) (hk : k ≠ 0)
    (hproj : Function.Surjective proj) : (transfer T C proj k).Reconstructed where
  axioms := hR.axioms
  faithful := hR.faithful
  injective := by
    intro d x y hxy
    have hxy' : k • T.toLabel d x = k • T.toLabel d y := hxy
    have h2 := congrArg (k⁻¹ • ·) hxy'
    simp only [smul_smul, inv_mul_cancel₀ hk, one_smul] at h2
    exact hR.injective d h2
  acts := by
    obtain ⟨a, f, h⟩ := hR.acts
    refine ⟨a, f, fun h0 => h ?_⟩
    have h0' : T.theory.fields.field (k • T.toLabel a.1 a.2) f = 0 := h0
    rw [map_smul, LinearMap.smul_apply] at h0'
    have h2 := congrArg (k⁻¹ • ·) h0'
    simp only [smul_smul, inv_mul_cancel₀ hk, one_smul, smul_zero] at h2
    exact h2
  covers := by
    intro l
    obtain ⟨a, ha⟩ := hR.covers (k⁻¹ • l)
    have ha' : T.toLabel a.1 a.2 = k⁻¹ • l := ha
    refine ⟨a, ?_⟩
    show k • T.toLabel a.1 a.2 = l
    rw [ha']
    first
    | exact smul_inv_smul₀ hk l
    | exact smul_inv_smul₀ hk (show T.labels.carrier from l)
  represents := hproj
  normalized := hR.normalized
  fullSupport := hR.fullSupport
  permutation := by
    intro s n a x hx π
    exact congrArg (fun w => k ^ n * w) (hR.permutation s a x hx π)
  smooth := by
    intro s n a
    first
    | exact contDiffOn_const.mul (hR.smooth s a)
    | exact (hR.smooth s a).const_smul (k ^ n)
  characterContinuity := by
    intro n a x h
    exact continuous_const.mul (hR.characterContinuity a x h)
  mixture := by
    intro n a x h
    show (∫ i, k ^ n * T.correlation (some i) a x ∂T.phaseMeasure) =
      k ^ n * T.correlation none a x
    rw [integral_const_mul, hR.mixture a x h]
  analytic := by
    intro n v space
    exact (hR.analytic v space).const_mul (k ^ n)
  root := by
    intro n v x h
    exact congrArg (fun w => k ^ n * w) (hR.root v x h)
  boundary := by
    intro n v height h tests
    have hb := (hR.boundary v height h tests).const_mul (k ^ n)
    rw [← inv_vacuumExpectation_smul] at hb
    refine hb.congr (fun r => ?_)
    rw [← integral_const_mul]
    congr 1
    funext x
    exact (mul_assoc _ _ _).symm

/-- For `r → 0⁺`, a constant factor is absorbed by halving the slack `ε`. -/
theorem eventually_absorb (K a ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, K * r ^ (a - ε / 2) ≤ r ^ (a - ε) := by
  have hc : ContinuousAt (fun r : ℝ => r ^ (ε / 2)) 0 :=
    Real.continuousAt_rpow_const 0 (ε / 2) (Or.inr (half_pos hε).le)
  have ht : Tendsto (fun r : ℝ => K * r ^ (ε / 2)) (𝓝 0) (𝓝 0) := by
    have h0 := hc.tendsto.const_mul K
    rwa [Real.zero_rpow (half_pos hε).ne', mul_zero] at h0
  have h1 : ∀ᶠ r : ℝ in 𝓝[>] 0, K * r ^ (ε / 2) < 1 :=
    nhdsWithin_le_nhds (ht.eventually (gt_mem_nhds one_pos))
  filter_upwards [h1, self_mem_nhdsWithin] with r hr1 hr0
  have hr0' : (0 : ℝ) < r := hr0
  have hsplit : r ^ (a - ε / 2) = r ^ (a - ε) * r ^ (ε / 2) := by
    rw [← Real.rpow_add hr0']; congr 1; ring
  have hpos : 0 < r ^ (a - ε) := Real.rpow_pos_of_pos hr0' _
  calc K * r ^ (a - ε / 2) = (K * r ^ (ε / 2)) * r ^ (a - ε) := by rw [hsplit]; ring
    _ ≤ 1 * r ^ (a - ε) := mul_le_mul_of_nonneg_right hr1.le hpos.le
    _ = r ^ (a - ε) := one_mul _

theorem coeff_alg (k c g : ℂ) (hk : k ≠ 0) (a b : ℕ) :
    k ^ a * k⁻¹ * c * (k ^ (1 + b) * g) = k ^ (a + b) * (c * g) := by
  have h : k⁻¹ * k = 1 := inv_mul_cancel₀ hk
  calc k ^ a * k⁻¹ * c * (k ^ (1 + b) * g) = k ^ a * k ^ b * (k⁻¹ * k) * (c * g) := by ring
    _ = k ^ (a + b) * (c * g) := by rw [h, mul_one, pow_add]

theorem transfer_remainder_eq (hk : k ≠ 0) {I J : Type} [Fintype I] [Fintype J]
    (s : Option (transfer T C proj k).Character) (a : I → (transfer T C proj k).Tag)
    (x : I → Spacetime) (b : J → (transfer T C proj k).Tag) (y : J → Spacetime)
    (o : Spacetime) (D : ℕ) :
    (transfer T C proj k).grouped s a x b y -
        ∑ j : Fin (D + 1), ∑ i : (transfer T C proj k).Channel j.val,
          (transfer T C proj k).coefficient a j.val i x o *
            (transfer T C proj k).grouped s
              (fun _ : Unit => ⟨j.val, (transfer T C proj k).actor j.val i⟩) (fun _ => o) b y =
      k ^ (Fintype.card I + Fintype.card J) * (T.grouped s a x b y -
        ∑ j : Fin (D + 1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
          T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y) := by
  rw [mul_sub, Finset.mul_sum, transfer_grouped]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [transfer_grouped]
  have hU : ∀ inst : Fintype Unit, @Fintype.card Unit inst = 1 := fun inst => by
    rw [Fintype.card_eq_one_iff]; exact ⟨(), fun _ => rfl⟩
  rw [hU]
  exact coeff_alg k _ _ hk _ _

theorem transfer_ope (hO : T.OperatorProductExpansion) (hk : k ≠ 0) :
    (transfer T C proj k).OperatorProductExpansion where
  coefficients := by
    intro I _ a M η ε hM hη hε j i
    filter_upwards [hO.coefficients a M η (ε / 2) hM hη (half_pos hε) j i,
      eventually_absorb ‖k ^ Fintype.card I * k⁻¹‖ ((j : ℝ) - T.weight a) ε hε] with r h1 h2
    intro x o hW
    exact (norm_mul (k ^ Fintype.card I * k⁻¹) (T.coefficient a j i x o)).le.trans
      ((mul_le_mul_of_nonneg_left (h1 x o hW) (norm_nonneg _)).trans h2)
  remainder := by
    intro I J _ _ a b M η c ε hM hη hc hε D
    filter_upwards [hO.remainder a b M η c (ε / 2) hM hη hc (half_pos hε) D,
      eventually_absorb ‖k ^ (Fintype.card I + Fintype.card J)‖ ((D : ℝ) + 1 - T.weight a) ε hε]
      with r h1 h2
    intro x o y hW hC s
    exact ((congrArg norm (transfer_remainder_eq T C proj k hk s a x b y o D)).trans
      (norm_mul (k ^ (Fintype.card I + Fintype.card J)) _)).le.trans
      ((mul_le_mul_of_nonneg_left (h1 x o y hW hC s) (norm_nonneg _)).trans h2)

theorem inv_wick_scale (c : ℂ) (r : ℝ) : ∀ terms : List (ℂ × Hierarchy.Track),
    Hierarchy.wickProfile (terms.map fun ct => (c * ct.1, ct.2)) r =
      c * Hierarchy.wickProfile terms r
  | [] => by simp [Hierarchy.wickProfile]
  | (c', t') :: l => by
    have ih := inv_wick_scale c r l
    simp only [Hierarchy.wickProfile, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]; ring

theorem transfer_trace (hk : k ≠ 0)
    (hc : ∀ f : TestFunction, inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0)
    (L : ℂ)
    (hS : Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) • T.traceTwo r) (𝓝[>] 0) (𝓝 L))
    (hX : ∀ terms : List (ℂ × Hierarchy.Track),
      ¬ T.traceTwo =ᶠ[𝓝[>] 0] Hierarchy.wickProfile terms)
    (hpos : 0 < 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4)
    (hkL : k ^ 2 * L = ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ) : ℂ)) :
    (transfer T C proj k).TraceTest where
  centered := by
    intro f
    show inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (k • T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0
    first
    | (rw [map_smul, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul,
        inner_smul_right, hc f, mul_zero])
    | (simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul, inner_smul_right, hc f,
        mul_zero])
  amplitudePositive := hpos
  shortDistance := by
    have h2 := hS.const_mul (k ^ 2)
    rw [hkL] at h2
    refine h2.congr (fun r => ?_)
    show k ^ 2 * ((r ^ 8 * (Real.log r⁻¹) ^ 2) • T.traceTwo r) =
      (r ^ 8 * (Real.log r⁻¹) ^ 2) • (k ^ 2 * T.traceTwo r)
    first
    | exact mul_smul_comm _ _ _
    | (rw [Complex.real_smul, Complex.real_smul]; ring)
  excludes := by
    intro terms h
    apply hX (terms.map fun ct => ((k ^ 2)⁻¹ * ct.1, ct.2))
    filter_upwards [h] with r hr
    rw [inv_wick_scale, ← hr, transfer_traceTwo, ← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 hk), one_mul]

theorem transfer_zero (hZ : ZeroInvisible T) : ZeroInvisible (transfer T C proj k) := by
  intro n w x h
  show k ^ n * T.correlation (some T.selected) w x = 0
  rw [hZ n w x h, mul_zero]

end Transfer

/-! ### C. `IsSimple` makes `amplitudePositive` automatic -/

theorem amplitude_pos (g : GaugeGroup) (hg : g.IsSimple) :
    0 < 3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 := by
  obtain ⟨⟨X, hX, Y, hY, hXY⟩, -⟩ := hg
  have hX0 : X ≠ 0 := by
    rintro rfl
    simp at hXY
  have hr : 0 < Module.finrank ℝ g.lieAlgebra := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨X, hX⟩, fun he => hX0 (congrArg Subtype.val he)⟩
  have hr' : (0 : ℝ) < Module.finrank ℝ g.lieAlgebra := by exact_mod_cast hr
  exact div_pos (mul_pos (by norm_num) hr') (pow_pos Real.pi_pos 4)

/-- Square root of `target / L`. -/
theorem exists_scale (g : GaugeGroup) (hg : g.IsSimple) (L : ℂ) (hL : L ≠ 0) :
    ∃ k : ℂ, k ≠ 0 ∧
      k ^ 2 * L = ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ) : ℂ) := by
  have hpos := amplitude_pos g hg
  obtain ⟨k, hk2⟩ := IsAlgClosed.exists_pow_nat_eq
    ((((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ)) : ℂ) / L) (by norm_num : 0 < 2)
  have hkL : k ^ 2 * L = ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ) : ℂ) := by
    first
    | rw [hk2, div_mul_cancel₀ _ hL]
    | (rw [hk2]; field_simp)
  refine ⟨k, ?_, hkL⟩
  rintro rfl
  have h0 : ((3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ) : ℂ) = 0 := by
    rw [← hkL]; ring
  have h1 : (3 * (Module.finrank ℝ g.lieAlgebra : ℝ) / Real.pi ^ 4 : ℝ) = 0 := by
    exact_mod_cast h0
  linarith

/-! ### D. Cross-group transfer and `JointExistence` from one continuum hierarchy -/

/-- From ONE hierarchy over ANY Wilson family of ANY group, satisfying `Reconstructed`, the OPE,
zero-tag invisibility, and the trace test with an ARBITRARY nonzero short-distance constant `L`
(no quadratic hypothesis), get the four continuum clauses over EVERY simple group. -/
theorem single_hierarchy_transfer {g₀ : GaugeGroup} {C₀ : WilsonFamily g₀} (T₀ : Hierarchy C₀)
    (hR : T₀.Reconstructed) (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀)
    (hc : ∀ f : TestFunction, inner ℂ T₀.theory.fields.vacuum.1
      (T₀.theory.fields.field (T₀.toLabel 4 T₀.centeredTrace) f T₀.theory.fields.vacuum).1 = 0)
    (L : ℂ) (hL : L ≠ 0)
    (hS : Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) • T₀.traceTwo r) (𝓝[>] 0) (𝓝 L))
    (hX : ∀ terms : List (ℂ × Hierarchy.Track),
      ¬ T₀.traceTwo =ᶠ[𝓝[>] 0] Hierarchy.wickProfile terms)
    (g : GaugeGroup) (hg : g.IsSimple) :
    ∃ (C : WilsonFamily g) (T : Hierarchy C),
      T.Reconstructed ∧ T.OperatorProductExpansion ∧ T.TraceTest ∧ ZeroInvisible T := by
  obtain ⟨μ, hμ, hH⟩ := exists_haar g
  obtain ⟨k, hk, hkL⟩ := exists_scale g hg L hL
  exact ⟨blindFamily μ hH T₀.Field, transfer T₀ (blindFamily μ hH T₀.Field) id k,
    transfer_reconstructed T₀ (blindFamily μ hH T₀.Field) id k hR hk Function.surjective_id,
    transfer_ope T₀ (blindFamily μ hH T₀.Field) id k hO hk,
    transfer_trace T₀ (blindFamily μ hH T₀.Field) id k hk hc L hS hX (amplitude_pos g hg) hkL,
    transfer_zero T₀ (blindFamily μ hH T₀.Field) id k hZ⟩

/-- (a) Cross-group transfer: neither simplicity of `g₁` nor a quadratic hypothesis is used. -/
theorem cross_group {g₁ : GaugeGroup} {C₁ : WilsonFamily g₁} (T₁ : Hierarchy C₁)
    (hR : T₁.Reconstructed) (hO : T₁.OperatorProductExpansion) (hT : T₁.TraceTest)
    (hZ : ZeroInvisible T₁) (g₂ : GaugeGroup) (hg₂ : g₂.IsSimple) :
    ∃ (C : WilsonFamily g₂) (T : Hierarchy C),
      T.Reconstructed ∧ T.OperatorProductExpansion ∧ T.TraceTest ∧ ZeroInvisible T :=
  single_hierarchy_transfer T₁ hR hO hZ hT.centered _
    (Complex.ofReal_ne_zero.mpr hT.amplitudePositive.ne') hT.shortDistance hT.excludes g₂ hg₂

/-- `JointExistence` follows from one continuum hierarchy, with any nonzero constant. -/
theorem jointExistence_of_single {g₀ : GaugeGroup} {C₀ : WilsonFamily g₀} (T₀ : Hierarchy C₀)
    (hR : T₀.Reconstructed) (hO : T₀.OperatorProductExpansion) (hZ : ZeroInvisible T₀)
    (hc : ∀ f : TestFunction, inner ℂ T₀.theory.fields.vacuum.1
      (T₀.theory.fields.field (T₀.toLabel 4 T₀.centeredTrace) f T₀.theory.fields.vacuum).1 = 0)
    (L : ℂ) (hL : L ≠ 0)
    (hS : Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) • T₀.traceTwo r) (𝓝[>] 0) (𝓝 L))
    (hX : ∀ terms : List (ℂ × Hierarchy.Track),
      ¬ T₀.traceTwo =ᶠ[𝓝[>] 0] Hierarchy.wickProfile terms) :
    JointExistence :=
  jointExistence_of_continuum fun g hg =>
    single_hierarchy_transfer T₀ hR hO hZ hc L hL hS hX g hg

/-- `JointExistence` follows from one group's continuum witness. -/
theorem jointExistence_of_one_group {g₁ : GaugeGroup} {C₁ : WilsonFamily g₁} (T₁ : Hierarchy C₁)
    (hR : T₁.Reconstructed) (hO : T₁.OperatorProductExpansion) (hT : T₁.TraceTest)
    (hZ : ZeroInvisible T₁) : JointExistence :=
  jointExistence_of_continuum fun g hg => cross_group T₁ hR hO hT hZ g hg

/-! ### E. The same normalization on a GENUINE lattice witness: scale the insertions too -/

/-- Multiply every lattice insertion by `k`. -/
def scaleFamily {g : GaugeGroup} (C : WilsonFamily g) (k : ℂ) : WilsonFamily g :=
  { C with insertion := fun N p v x U => k * C.insertion N p v x U }

theorem scaleFamily_regular {g : GaugeGroup} (C : WilsonFamily g) (k : ℂ)
    (h : WilsonRegularity C) : WilsonRegularity (scaleFamily C k) where
  running := h.running
  continuous N p v x := continuous_const.mul (h.continuous N p v x)
  invariant N p v x t U := congrArg (fun w => k * w) (h.invariant N p v x t U)
  localSupport v := by
    obtain ⟨stencil, hs⟩ := h.localSupport v
    refine ⟨stencil, fun N p x => ?_⟩
    intro sites U V hUV
    exact congrArg (fun w => k * w) (hs N p x U V hUV)

theorem scaleFamily_finiteMoment {g : GaugeGroup} (C : WilsonFamily g) (k : ℂ) (N p : ℕ)
    {n : ℕ} (v : Fin n → C.Token) (x : Fin n → Site (C.period p * C.denominator N)) :
    (scaleFamily C k).finiteMoment N p v x = k ^ n * C.finiteMoment N p v x := by
  show ∫ U, ∏ i, (k * C.insertion N p (v i) (x i) U)
      ∂wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar =
    k ^ n * ∫ U, ∏ i, C.insertion N p (v i) (x i) U
      ∂wilsonLaw g (C.period p * C.denominator N) (C.beta N p) C.haar
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact integral_const_mul _ _

theorem scaleFamily_smear {g : GaugeGroup} (C : WilsonFamily g) (k : ℂ) (N p : ℕ) {n : ℕ}
    (v : Fin n → C.Token) (t : WilsonFamily.SeparatedTest n) :
    (scaleFamily C k).smear N p v t = k ^ n * C.smear N p v t := by
  show (C.mesh N : ℂ) ^ (4 * n) * ∑ x : Fin n → Site (C.period p * C.denominator N),
      t (WithLp.toLp 2 fun i => C.place N p (x i)) * (scaleFamily C k).finiteMoment N p v x =
    k ^ n * ((C.mesh N : ℂ) ^ (4 * n) * ∑ x : Fin n → Site (C.period p * C.denominator N),
      t (WithLp.toLp 2 fun i => C.place N p (x i)) * C.finiteMoment N p v x)
  simp only [scaleFamily_finiteMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  ring

theorem scaleFamily_converges {g : GaugeGroup} (C : WilsonFamily g) (k : ℂ) (order : ℕ → ℕ)
    (u : {n : ℕ} → (Fin n → C.Token) → Points n → ℂ) (h : C.Converges order u) :
    (scaleFamily C k).Converges order (fun {n} v x => k ^ n * u v x) := by
  intro n v t
  obtain ⟨hs, row, hrow, hlim⟩ := h n v t
  refine ⟨hs, fun p => k ^ n * row p, fun p hp => ?_, ?_⟩
  · exact ((hrow p hp).const_mul (k ^ n)).congr
      (fun N => (scaleFamily_smear C k N p v t).symm)
  · have e : ∫ x, t x * (k ^ n * u v x) = k ^ n * ∫ x, t x * u v x := by
      rw [← integral_const_mul]; congr 1; funext x; ring
    have h2 := hlim.const_mul (k ^ n)
    rw [← e] at h2
    exact h2

/-- `Properties` with the trace constant `3 dim g / π⁴` replaced by an arbitrary `L`. -/
def PropertiesL {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C) (order : ℕ → ℕ)
    (L : ℂ) : Prop :=
  C.Converges order (fun v => T.correlation none (T.project ∘ v)) ∧ T.Reconstructed ∧
    T.OperatorProductExpansion ∧
    (∀ f : TestFunction, inner ℂ T.theory.fields.vacuum.1
      (T.theory.fields.field (T.toLabel 4 T.centeredTrace) f T.theory.fields.vacuum).1 = 0) ∧
    Tendsto (fun r : ℝ => (r ^ 8 * (Real.log r⁻¹) ^ 2) • T.traceTwo r) (𝓝[>] 0) (𝓝 L) ∧
    (∀ terms : List (ℂ × Hierarchy.Track), ¬ T.traceTwo =ᶠ[𝓝[>] 0] Hierarchy.wickProfile terms)

/-- The per-group clause of `JointExistence` with ANY fixed nonzero trace constant implies the
clause with the exact constant, keeping a genuine Wilson family up to rescaled insertions.
No quadratic hypothesis and no zero-tag hypothesis. -/
theorem perGroup_of_any_constant (g : GaugeGroup) (hg : g.IsSimple) (L : ℂ) (hL : L ≠ 0)
    (h : ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
      ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, PropertiesL T (p ∘ q) L) :
    ∃ C : WilsonFamily g, WilsonRegularity C ∧ ∀ p : ℕ → ℕ, StrictMono p →
      ∃ q : ℕ → ℕ, StrictMono q ∧ ∃ T : Hierarchy C, T.Properties (p ∘ q) := by
  obtain ⟨C, hC, hall⟩ := h
  obtain ⟨k, hk, hkL⟩ := exists_scale g hg L hL
  refine ⟨scaleFamily C k, scaleFamily_regular C k hC, fun p hp => ?_⟩
  obtain ⟨q, hq, T, hW, hR, hO, hc, hS, hX⟩ := hall p hp
  exact ⟨q, hq, transfer T (scaleFamily C k) T.project k,
    scaleFamily_converges C k (p ∘ q) _ hW,
    transfer_reconstructed T (scaleFamily C k) T.project k hR hk hR.represents,
    transfer_ope T (scaleFamily C k) T.project k hO hk,
    transfer_trace T (scaleFamily C k) T.project k hk hc L hS hX (amplitude_pos g hg) hkL⟩

end InventoryTransfer

/-! ### F. (c) The real dimension of the SU(2) Lie algebra in the statement's ℝ-module -/

namespace InventorySU2
open YangMills Matrix

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
/-- The three matrices of `YM/Examples/SU2.lean` lines 16-18. -/
def A : M2 := !![Complex.I, 0; 0, -Complex.I]
def B : M2 := !![0, 1; -1, 0]
def Cm : M2 := !![0, Complex.I; Complex.I, 0]

/-- The `ℝ`-action used by `GaugeGroup.lieAlgebra` is entrywise multiplication by `(r : ℂ)`. -/
example (r : ℝ) (X : Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ) (i j : Fin (1 + 1)) :
    (r • X) i j = (r : ℂ) * X i j := rfl

/-- The ambient real dimension is `8`, so the `ℝ`-structure is the restriction of scalars. -/
theorem finrank_ambient : Module.finrank ℝ (Matrix (Fin 2) (Fin 2) ℂ) = 8 := by
  first
  | (rw [Module.finrank_matrix, Complex.finrank_real_complex]; simp)
  | simp [Module.finrank_matrix, Complex.finrank_real_complex]

theorem linIndep : LinearIndependent ℝ ![A, B, Cm] := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h00 := congrArg (fun X : M2 => (X 0 0).im) hc
  have h01r := congrArg (fun X : M2 => (X 0 1).re) hc
  have h01i := congrArg (fun X : M2 => (X 0 1).im) hc
  simp [Fin.sum_univ_three, A, B, Cm] at h00 h01r h01i
  intro i
  fin_cases i
  · first | exact h00 | simpa using h00
  · first | exact h01r | simpa using h01r
  · first | exact h01i | simpa using h01i

theorem finrank_span : Module.finrank ℝ (Submodule.span ℝ (Set.range ![A, B, Cm])) = 3 := by
  rw [finrank_span_eq_card linIndep]; simp

/-- Any gauge group in the two-dimensional defining representation (`n = 1`) whose Lie algebra
contains `A, B, C` and is spanned by them has real dimension `3`.  `ConcreteSU2.su2` is of this
form (`ConcreteSU2.lean:8-10` with `SUtwo.n := 1`), and the four hypotheses are the private
lemmas `a_in`, `b_in`, `c_in`, `express` of `YM/Examples/SU2.lean`. -/
theorem lieAlgebra_finrank (image : Subgroup (UnitaryRepresentation 1))
    (hcl : IsClosed (image : Set (UnitaryRepresentation 1)))
    (L : Submodule ℝ (Matrix (Fin (1 + 1)) (Fin (1 + 1)) ℂ)) (gen : _)
    (hA : A ∈ L) (hB : B ∈ L) (hC : Cm ∈ L)
    (hexp : ∀ X ∈ L, ∃ a b c : ℝ, X = a • A + b • B + c • Cm) :
    Module.finrank ℝ (GaugeGroup.mk 1 image hcl L gen).lieAlgebra = 3 := by
  have hL : L = Submodule.span ℝ (Set.range ![A, B, Cm]) := by
    apply le_antisymm
    · intro X hX
      obtain ⟨a, b, c, rfl⟩ := hexp X hX
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨![a, b, c], by simp [Fin.sum_univ_three]⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i
      · first | exact hA | simpa using hA
      · first | exact hB | simpa using hB
      · first | exact hC | simpa using hC
  show Module.finrank ℝ L = 3
  rw [hL]
  exact finrank_span

end InventorySU2

/-! ### G. The OPE aliases are definitional copies of existing carriers -/
namespace InventoryAliases
open YangMills
example : Hierarchy.OPEPoint = Spacetime := rfl
example (n : ℕ) : Hierarchy.OPEPoints n = Points n := rfl
example (n : ℕ) : Hierarchy.OPEComplexTimes n = (Fin n → ℂ) := rfl
example (n : ℕ) : Hierarchy.OPESpacePoints n = (Fin n → Space) := rfl
end InventoryAliases

#print axioms InventoryTransfer.inv_vacuumExpectation_smul
#print axioms InventoryTransfer.transfer_reconstructed
#print axioms InventoryTransfer.transfer_ope
#print axioms InventoryTransfer.transfer_trace
#print axioms InventoryTransfer.single_hierarchy_transfer
#print axioms InventoryTransfer.cross_group
#print axioms InventoryTransfer.jointExistence_of_single
#print axioms InventoryTransfer.jointExistence_of_one_group
#print axioms InventoryTransfer.perGroup_of_any_constant
#print axioms InventorySU2.finrank_ambient
#print axioms InventorySU2.finrank_span
#print axioms InventorySU2.lieAlgebra_finrank
set_option pp.proofs false in
#check @InventoryTransfer.jointExistence_of_single
#check @InventoryTransfer.cross_group
#check @InventoryTransfer.perGroup_of_any_constant
#check @InventorySU2.lieAlgebra_finrank
