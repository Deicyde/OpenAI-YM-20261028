import ChallengeSpec

/-! Audit probe (group: lattice-to-continuum limit and Wilson regularity,
PublicWilson.lean lines 59-90 and ChallengeSpec.lean lines 11-22).

(A) the first conjunct of `Converges` holds automatically along any strictly increasing order;
(B) `smear` is a correctly normalised Riemann sum (`riemann_tendsto`, argument copied from
    Audit/Reduction/Riemann.lean);
(C) every family whose finite moments are constants `c v` satisfies `Converges` with the
    constant correlation `c v`;
(D) a family whose insertions never read the links satisfies `WilsonRegularity` for every
    positive slope and `Converges` along every strictly increasing volume order;
(E) the gauge action in `WilsonRegularity.invariant` conjugates the plaquette, so plaquette
    traces (genuine Wilson observables) satisfy the `invariant` and `continuous` clauses. -/

set_option autoImplicit false
noncomputable section

namespace YMProbeWilsonLimit
open YangMills MeasureTheory Filter Topology Set
open scoped ENNReal

/-! ## Wilson-law facts (same proofs as Audit/Probes/wilsonlaw_semantics.lean) -/

theorem isCompact_unitaryGroup (k : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  refine (IsCompact.matrix (isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
    isClosed_unitary ?_
  intro U hU i j
  simpa using entry_norm_bound_of_unitary hU i j

theorem compactSpace_image (g : GaugeGroup) : CompactSpace g.image := by
  haveI : CompactSpace (UnitaryRepresentation g.n) :=
    isCompact_iff_compactSpace.mp (isCompact_unitaryGroup (g.n + 1))
  exact isCompact_iff_compactSpace.mp g.imageClosed.isCompact

theorem exists_haar (g : GaugeGroup) :
    ∃ μ : Measure g.image, IsProbabilityMeasure μ ∧ μ.IsHaarMeasure := by
  haveI := compactSpace_image g
  refine ⟨Measure.haarMeasure ⊤, ⟨?_⟩, inferInstance⟩
  have h := Measure.haarMeasure_self (G := g.image) (K₀ := ⊤)
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

theorem secondCountable_image (g : GaugeGroup) : SecondCountableTopology g.image := by
  haveI : SecondCountableTopology (Matrix (Fin (g.n + 1)) (Fin (g.n + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (g.n + 1) → Fin (g.n + 1) → ℂ))
  haveI : SecondCountableTopology (UnitaryRepresentation g.n) := by
    exact Topology.IsInducing.subtypeVal.secondCountableTopology
  exact Topology.IsInducing.subtypeVal.secondCountableTopology

theorem continuous_plaquette (g : GaugeGroup) (l : ℕ+) (x : Site l) (i j : Axis) :
    Continuous fun U : Configuration g l => plaquette U x i j := by
  unfold plaquette
  first
  | fun_prop
  | exact (continuous_apply _).mul ((continuous_apply _).mul
      ((continuous_apply _).inv.mul (continuous_apply _).inv))

theorem continuous_wilsonEnergy (g : GaugeGroup) (l : ℕ+) :
    Continuous fun U : Configuration g l => wilsonEnergy U := by
  unfold wilsonEnergy
  refine continuous_finsetSum _ fun p _ => continuous_const.sub (Continuous.div_const ?_ _)
  exact Complex.continuous_re.comp
    ((continuous_subtype_val.comp (continuous_subtype_val.comp
      (continuous_plaquette g l p.1 p.2.val.1 p.2.val.2))).matrix_trace)

theorem wilsonLaw_isProbability (g : GaugeGroup) (l : ℕ+) (β : ℝ) (μ : Measure g.image)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (wilsonLaw g l β μ) := by
  haveI : CompactSpace g.image := compactSpace_image g
  haveI : SecondCountableTopology g.image := secondCountable_image g
  haveI : IsFiniteMeasureOnCompacts (Measure.pi fun _ : Site l × Axis => μ) :=
    ⟨fun K _ => measure_lt_top _ K⟩
  have hd : Continuous fun U : Configuration g l => Real.exp (-β * wilsonEnergy U) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_wilsonEnergy g l))
  have hi : Integrable (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U))
      (Measure.pi fun _ : Site l × Axis => μ) :=
    hd.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hZ : 0 < ∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Site l × Axis => μ) := by
    rw [integral_pos_iff_support_of_nonneg (fun U => (Real.exp_pos _).le) hi]
    have hs : Function.support (fun U : Configuration g l => Real.exp (-β * wilsonEnergy U))
        = Set.univ := Set.eq_univ_of_forall fun U => (Real.exp_pos _).ne'
    rw [hs, measure_univ]
    exact one_pos
  constructor
  show ((Measure.pi fun _ : Site l × Axis => μ).withDensity fun U => ENNReal.ofReal
      (Real.exp (-β * wilsonEnergy U) / ∫ V, Real.exp (-β * wilsonEnergy V)
        ∂(Measure.pi fun _ : Site l × Axis => μ))) Set.univ = 1
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (hi.div_const (∫ V, Real.exp (-β * wilsonEnergy V) ∂(Measure.pi fun _ : Site l × Axis => μ)))
      (Eventually.of_forall fun U => div_nonneg (Real.exp_pos _).le hZ.le),
    integral_div, div_self hZ.ne', ENNReal.ofReal_one]

/-- Insertions that do not read `U` have finite moments equal to the product of their values. -/
theorem finiteMoment_of_blind (g : GaugeGroup) (C : WilsonFamily g)
    (h : ∀ N p : ℕ, C.Token → Site (C.period p * C.denominator N) → ℂ)
    (hC : ∀ N p v x U, C.insertion N p v x U = h N p v x) (N p : ℕ) {n : ℕ}
    (labels : Fin n → C.Token) (x : Fin n → Site (C.period p * C.denominator N)) :
    C.finiteMoment N p labels x = ∏ i, h N p (labels i) (x i) := by
  haveI := C.probability
  haveI := wilsonLaw_isProbability g (C.period p * C.denominator N) (C.beta N p) C.haar
  unfold WilsonFamily.finiteMoment
  simp_rw [hC]
  simp [integral_const, probReal_univ]

/-! ## (B) Riemann sums (argument of Audit/Reduction/Riemann.lean, lines 9-195) -/
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

/-! ## (A) The first conjunct of `Converges` is automatic -/

theorem eventually_suitable {g : GaugeGroup} (C : WilsonFamily g) {order : ℕ → ℕ}
    (ho : StrictMono order) {n : ℕ} (t : WilsonFamily.SeparatedTest n) :
    ∀ᶠ k in atTop, C.suitable (order k) t := by
  obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.1
    (show IsCompact (tsupport (t : Points n → ℂ)) from t.hasCompactSupport).isBounded
  have hmono : StrictMono fun k => (C.period (order k)).val := C.periodStrict.comp ho
  have htend : Tendsto (fun k => ((C.period (order k)).val : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmono.tendsto_atTop
  filter_upwards [htend.eventually_gt_atTop (2 * R)] with k hk
  unfold WilsonFamily.suitable
  intro x hx
  rw [Set.mem_setOf_eq]
  intro i a
  have h1 := PiLp.norm_apply_le (x i) a
  have h2 := PiLp.norm_apply_le x i
  have h3 := hR x hx
  rw [Real.norm_eq_abs] at h1
  have h4 := abs_le.1 (h1.trans (h2.trans h3))
  constructor <;> linarith [h4.1, h4.2]

/-! ## (C) Constant finite moments converge -/

theorem const_converges {g : GaugeGroup} (C : WilsonFamily g) {order : ℕ → ℕ}
    (ho : StrictMono order) (c : {n : ℕ} → (Fin n → C.Token) → ℂ)
    (hm : ∀ (N p : ℕ) {n : ℕ} (v : Fin n → C.Token)
      (x : Fin n → Site (C.period p * C.denominator N)), C.finiteMoment N p v x = c v) :
    C.Converges order (fun v _ => c v) := by
  intro n v t
  refine ⟨eventually_suitable C ho t, fun _ => c v * ∫ x, t x, fun p hp => ?_, ?_⟩
  · refine ((riemann_tendsto C p t hp).const_mul (c v)).congr fun N => ?_
    simp only [WilsonFamily.smear, hm, ← Finset.sum_mul]
    ring
  · have e : (∫ x, t x * c v) = c v * ∫ x, t x := by
      rw [integral_mul_const, mul_comm]
    first
    | (simp only [e]; exact tendsto_const_nhds)
    | (show Tendsto (fun _ => c v * ∫ x, t x) atTop (𝓝 (∫ x, t x * c v))
       rw [e]; exact tendsto_const_nhds)

/-! ## (D) A family that never reads the links meets both lattice clauses -/

/-- Constant insertions, slope `s` for `beta`. -/
def blindConst (g : GaugeGroup) (μ : Measure g.image) [hμ : IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (s : ℝ) (Tok : Type) (c : Tok → ℂ) : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict a b hab := by show a + 1 < b + 1; omega
  denominatorStrict a b hab := by show a + 2 < b + 2; omega
  beta N _ := s * Real.log ((N + 2 : ℕ) : ℝ)
  haar := μ
  probability := hμ
  invariantHaar := hH
  Token := Tok
  insertion _ _ v _ _ := c v

/-- `running` holds for every positive slope: it does not pin the asymptotic-freedom slope. -/
theorem blindConst_regular (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (s : ℝ) (hs : 0 < s) (Tok : Type) (c : Tok → ℂ) :
    WilsonRegularity (blindConst g μ hH s Tok c) := by
  refine ⟨⟨s, hs, fun ε hε => Eventually.of_forall fun N p => ?_⟩,
    fun _ _ _ _ => continuous_const, fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨∅, fun _ _ _ => by intro sites U V _; rfl⟩⟩
  have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
  have hd : (blindConst g μ hH s Tok c).beta N p /
      Real.log ((blindConst g μ hH s Tok c).mesh N)⁻¹ = s := by
    show s * Real.log ((N + 2 : ℕ) : ℝ) / Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = s
    rw [inv_inv, mul_div_assoc, div_self hpos.ne', mul_one]
  rw [hd, sub_self, abs_zero]
  exact hε

theorem blindConst_converges (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (s : ℝ) (Tok : Type) (c : Tok → ℂ) {order : ℕ → ℕ}
    (ho : StrictMono order) :
    (blindConst g μ hH s Tok c).Converges order (fun v _ => ∏ i, c (v i)) :=
  const_converges (blindConst g μ hH s Tok c) ho (fun v => ∏ i, c (v i))
    (fun N p _ v x => finiteMoment_of_blind g (blindConst g μ hH s Tok c) (fun _ _ v _ => c v)
      (fun _ _ _ _ _ => rfl) N p v x)

/-- For every gauge group, every token type and every choice of constants, some Wilson family
satisfies `WilsonRegularity` and `Converges` along every strictly increasing volume order, with
limit the constant product `∏ c`. No lattice integral is ever evaluated. -/
theorem lattice_clauses_without_lattice (g : GaugeGroup) (s : ℝ) (hs : 0 < s) (Tok : Type)
    (c : Tok → ℂ) :
    ∃ C : WilsonFamily g, ∃ π : C.Token → Tok, Function.Bijective π ∧ WilsonRegularity C ∧
      ∀ order : ℕ → ℕ, StrictMono order →
        C.Converges order (fun v _ => ∏ i, c (π (v i))) := by
  obtain ⟨μ, hμ, hH⟩ := exists_haar g
  haveI := hμ
  exact ⟨blindConst g μ hH s Tok c, id, Function.bijective_id,
    blindConst_regular g μ hH s hs Tok c, fun order ho => blindConst_converges g μ hH s Tok c ho⟩

/-! ## (E) The gauge action of `invariant` matches the plaquette orientation -/

theorem plaquette_gauge {g : GaugeGroup} {l : ℕ+} (U : Configuration g l)
    (t : Site l → g.image) (x : Site l) (i j : Axis) :
    plaquette (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) x i j =
      t x * plaquette U x i j * (t x)⁻¹ := by
  unfold plaquette
  try dsimp only
  rw [add_right_comm x (Pi.single i 1) (Pi.single j 1)]
  first
  | group
  | simp only [mul_assoc, mul_inv_rev, inv_inv, inv_mul_cancel_left]

theorem trace_conj {g : GaugeGroup} (a b : g.image) :
    (a * b * a⁻¹).val.val.trace = b.val.val.trace := by
  have h1 : (a * b * a⁻¹).val.val = a.val.val * b.val.val * (a⁻¹).val.val := rfl
  have h2 : (a⁻¹).val.val * a.val.val = 1 := by
    have h : ((a⁻¹ * a : g.image)).val.val = ((1 : g.image)).val.val := by rw [inv_mul_cancel]
    exact h
  rw [h1, Matrix.trace_mul_cycle, h2, one_mul]

theorem trace_plaquette_invariant {g : GaugeGroup} {l : ℕ+} (U : Configuration g l)
    (t : Site l → g.image) (x : Site l) (i j : Axis) :
    (plaquette (fun e => t e.1 * U e * (t (e.1 + Pi.single e.2 1))⁻¹) x i j).val.val.trace =
      (plaquette U x i j).val.val.trace := by
  rw [plaquette_gauge, trace_conj]

theorem continuous_trace_plaquette (g : GaugeGroup) (l : ℕ+) (x : Site l) (i j : Axis) :
    Continuous fun U : Configuration g l => (plaquette U x i j).val.val.trace :=
  (continuous_subtype_val.comp (continuous_subtype_val.comp
    (continuous_plaquette g l x i j))).matrix_trace

/-! ## (F) Genuinely link-dependent families satisfy `WilsonRegularity`, with an arbitrary
`N`- and `p`-dependent nonlinear functional form -/

/-- Insertion: `f N p` applied to the trace of the (0,1) plaquette at the site. -/
def plaqFamilyF (g : GaugeGroup) (μ : Measure g.image) [hμ : IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (f : ℕ → ℕ → ℂ → ℂ) : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict a b hab := by show a + 1 < b + 1; omega
  denominatorStrict a b hab := by show a + 2 < b + 2; omega
  beta N _ := Real.log ((N + 2 : ℕ) : ℝ)
  haar := μ
  probability := hμ
  invariantHaar := hH
  Token := Unit
  insertion N p _ x U := f N p (plaquette U x 0 1).val.val.trace

theorem cast_single (m : ℕ) (k : Axis) :
    (fun i => (((Pi.single k (1 : ℤ) : Axis → ℤ) i : ℤ) : ZMod m)) = Pi.single k (1 : ZMod m) := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

theorem plaqFamilyF_regular (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (f : ℕ → ℕ → ℂ → ℂ) (hf : ∀ N p, Continuous (f N p)) :
    WilsonRegularity (plaqFamilyF g μ hH f) := by
  refine ⟨⟨1, one_pos, fun ε hε => Eventually.of_forall fun N p => ?_⟩,
    fun N p v x => (hf N p).comp (continuous_trace_plaquette g _ x 0 1),
    fun N p v x t U => congrArg (f N p) (trace_plaquette_invariant U t x 0 1), fun v => ?_⟩
  · have hpos : 0 < Real.log ((N + 2 : ℕ) : ℝ) := Real.log_pos (by norm_cast; omega)
    have hd : (plaqFamilyF g μ hH f).beta N p /
        Real.log ((plaqFamilyF g μ hH f).mesh N)⁻¹ = 1 := by
      show Real.log ((N + 2 : ℕ) : ℝ) / Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = 1
      rw [inv_inv, div_self hpos.ne']
    rw [hd, sub_self, abs_zero]
    exact hε
  · refine ⟨{0, Pi.single 0 1, Pi.single 1 1, Pi.single 0 1 + Pi.single 1 1}, fun N p x => ?_⟩
    intro sites U V hUV
    have hmem : ∀ z ∈ ({0, Pi.single 0 1, Pi.single 1 1, Pi.single 0 1 + Pi.single 1 1} :
        Finset (Axis → ℤ)), (fun i => ((z i : ℤ) : ZMod
          ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val)) + x ∈
            sites :=
      fun z hz => Finset.mem_image_of_mem _ hz
    have s0 : x ∈ sites := by
      have h := hmem 0 (Finset.mem_insert_self _ _)
      have e : (fun i => (((0 : Axis → ℤ) i : ℤ) : ZMod
          ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val)) + x =
            x := by
        funext i
        show (((0 : ℤ)) : ZMod
          ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val) + x i =
            x i
        rw [Int.cast_zero, zero_add]
      rwa [e] at h
    have s1 : x + Pi.single 0 1 ∈ sites := by
      have h := hmem (Pi.single 0 1) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      rwa [cast_single, add_comm] at h
    have s2 : x + Pi.single 1 1 ∈ sites := by
      have h := hmem (Pi.single 1 1)
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      rwa [cast_single, add_comm] at h
    have s3 : x + Pi.single 0 1 + Pi.single 1 1 ∈ sites := by
      have h := hmem (Pi.single 0 1 + Pi.single 1 1) (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
      have e1 : (fun i => ((((Pi.single 0 1 + Pi.single 1 1 : Axis → ℤ)) i : ℤ) : ZMod
          ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val)) =
          (fun i => ((((Pi.single 0 (1 : ℤ) : Axis → ℤ)) i : ℤ) : ZMod
            ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val)) +
          (fun i => ((((Pi.single 1 (1 : ℤ) : Axis → ℤ)) i : ℤ) : ZMod
            ((plaqFamilyF g μ hH f).period p * (plaqFamilyF g μ hH f).denominator N).val)) := by
        funext i; simp only [Pi.add_apply, Int.cast_add]
      rw [e1, cast_single, cast_single, add_comm, ← add_assoc] at h
      exact h
    have s3' : x + Pi.single 1 1 + Pi.single 0 1 ∈ sites := by rwa [add_right_comm]
    show f N p (plaquette U x 0 1).val.val.trace = f N p (plaquette V x 0 1).val.val.trace
    unfold plaquette
    rw [hUV (x, 0) s0 s1, hUV (x + Pi.single 0 1, 1) s1 s3,
      hUV (x + Pi.single 1 1, 0) s2 s3', hUV (x, 1) s0 s2]

/-- The plain plaquette-trace family, and an `N`-dependent nonlinear one. -/
example (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure) :
    WilsonRegularity (plaqFamilyF g μ hH fun _ _ z => z) :=
  plaqFamilyF_regular g μ hH _ fun _ _ => continuous_id
example (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ] (hH : μ.IsHaarMeasure) :
    WilsonRegularity (plaqFamilyF g μ hH fun N p z => (N : ℂ) ^ p * z ^ N) :=
  plaqFamilyF_regular g μ hH _ fun N p => continuous_const.mul (continuous_pow N)

/-! ## (G) `running` also allows an unbounded subleading drift of the bare coupling -/

theorem running_drift (s ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ _p : ℕ,
      |(s * Real.log ((N + 2 : ℕ) : ℝ) + Real.sqrt (Real.log ((N + 2 : ℕ) : ℝ))) /
        Real.log ((N + 2 : ℕ) : ℝ) - s| < ε := by
  have hlog : Tendsto (fun N : ℕ => Real.log ((N + 2 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
  filter_upwards [hlog.eventually_gt_atTop ((ε⁻¹) ^ 2)] with N hN _p
  set L := Real.log ((N + 2 : ℕ) : ℝ) with hL
  have hε2 : 0 < (ε⁻¹) ^ 2 := by positivity
  have hLpos : 0 < L := lt_trans hε2 hN
  have hL0 : L ≠ 0 := hLpos.ne'
  have hsq : ε⁻¹ < Real.sqrt L := by
    rw [show ε⁻¹ = Real.sqrt ((ε⁻¹) ^ 2) from (Real.sqrt_sq (inv_pos.2 hε).le).symm]
    exact Real.sqrt_lt_sqrt hε2.le hN
  have hsqpos : 0 < Real.sqrt L := Real.sqrt_pos.2 hLpos
  have key : (s * L + Real.sqrt L) / L - s = Real.sqrt L / L := by
    rw [add_div, mul_div_assoc, div_self hL0, mul_one, add_sub_cancel_left]
  rw [key, abs_of_pos (div_pos hsqpos hLpos), div_lt_iff₀ hLpos]
  have h1 : 1 < ε * Real.sqrt L := by
    have := mul_lt_mul_of_pos_left hsq hε
    rwa [mul_inv_cancel₀ hε.ne'] at this
  calc Real.sqrt L = 1 * Real.sqrt L := (one_mul _).symm
    _ < (ε * Real.sqrt L) * Real.sqrt L := mul_lt_mul_of_pos_right h1 hsqpos
    _ = ε * L := by rw [mul_assoc, Real.mul_self_sqrt hLpos.le]

/-- Gauge-blind family with drifting coupling `β = s log D + √(log D)`. -/
def driftFamily (g : GaugeGroup) (μ : Measure g.image) [hμ : IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (s : ℝ) (Tok : Type) (c : Tok → ℂ) : WilsonFamily g where
  period p := ⟨p + 1, Nat.succ_pos p⟩
  denominator N := ⟨N + 2, by omega⟩
  periodStrict a b hab := by show a + 1 < b + 1; omega
  denominatorStrict a b hab := by show a + 2 < b + 2; omega
  beta N _ := s * Real.log ((N + 2 : ℕ) : ℝ) + Real.sqrt (Real.log ((N + 2 : ℕ) : ℝ))
  haar := μ
  probability := hμ
  invariantHaar := hH
  Token := Tok
  insertion _ _ v _ _ := c v

theorem driftFamily_regular (g : GaugeGroup) (μ : Measure g.image) [IsProbabilityMeasure μ]
    (hH : μ.IsHaarMeasure) (s : ℝ) (hs : 0 < s) (Tok : Type) (c : Tok → ℂ) :
    WilsonRegularity (driftFamily g μ hH s Tok c) := by
  refine ⟨⟨s, hs, fun ε hε => ?_⟩, fun _ _ _ _ => continuous_const, fun _ _ _ _ _ _ => rfl,
    fun _ => ⟨∅, fun _ _ _ => by intro sites U V _; rfl⟩⟩
  filter_upwards [running_drift s ε hε] with N hN p
  have e : (driftFamily g μ hH s Tok c).beta N p /
      Real.log ((driftFamily g μ hH s Tok c).mesh N)⁻¹ =
      (s * Real.log ((N + 2 : ℕ) : ℝ) + Real.sqrt (Real.log ((N + 2 : ℕ) : ℝ))) /
        Real.log ((N + 2 : ℕ) : ℝ) := by
    show (s * Real.log ((N + 2 : ℕ) : ℝ) + Real.sqrt (Real.log ((N + 2 : ℕ) : ℝ))) /
      Real.log ((((N + 2 : ℕ) : ℝ))⁻¹)⁻¹ = _
    rw [inv_inv]
  rw [e]
  exact hN p

#print axioms eventually_suitable
#print axioms riemann_tendsto
#print axioms const_converges
#print axioms blindConst_regular
#print axioms blindConst_converges
#print axioms lattice_clauses_without_lattice
#print axioms trace_plaquette_invariant
#print axioms continuous_trace_plaquette
#print axioms plaqFamilyF_regular
#print axioms running_drift
#print axioms driftFamily_regular

end YMProbeWilsonLimit
