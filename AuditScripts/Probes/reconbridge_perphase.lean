import ChallengeSpec

/-! Audit probe (repair R1: per-character reconstruction).

If a character `i` carries its own one-point continuation with the public `analytic`,
`root` and `boundary` shapes (into ANY field system over the hierarchy's labels, read through
the hierarchy's linear `toLabel`), then its correlation on the one-point word of the zero
vector of grade 0 cannot be a nonzero constant.  In the compiled reduction
(`Audit/Reduction/Defs.lean`), the second phase is `2 * allZero - S`, which equals the
constant `2` on that word once `ZeroInvisible` holds; so R1 refutes that phase. -/

set_option autoImplicit false
noncomputable section

namespace ReconBridgePerPhase
open YangMills MeasureTheory Filter Topology Set
open scoped ContDiff

theorem orderedTube_one : Hierarchy.orderedTube 1 = Set.univ := by
  refine Set.eq_univ_of_forall fun z => ?_
  show StrictMono fun i : Fin 1 => (z i).im
  intro a b hab
  exact absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)

theorem vector_eq_zero {H : YangMills.HilbertSpace} {L : FieldLabels} (F : FieldSystem H L)
    (w : List (L.carrier × YangMills.TestFunction)) (h : ∃ p ∈ w, p.1 = 0) :
    F.vector w = 0 := by
  induction w with
  | nil => simp at h
  | cons q w ih =>
    show F.field q.1 q.2 (F.vector w) = 0
    by_cases hq : q.1 = 0
    · rw [hq, map_zero, LinearMap.zero_apply, LinearMap.zero_apply]
    · obtain ⟨p, hp, hp0⟩ := h
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact absurd hp0 hq
      · rw [ih ⟨p, hp', hp0⟩, map_zero]

theorem vacuumExpectation_zero_label {H : YangMills.HilbertSpace} {L : FieldLabels}
    (F : FieldSystem H L) {n : ℕ} (labels : Fin n → L.carrier)
    (tests : Fin n → YangMills.TestFunction) (k : Fin n) (hk : labels k = 0) :
    F.vacuumExpectation labels tests = 0 := by
  unfold FieldSystem.vacuumExpectation
  rw [vector_eq_zero F (List.ofFn fun i => (labels i, tests i))
    ⟨(labels k, tests k), (List.mem_ofFn' _ _).mpr ⟨k, rfl⟩, hk⟩]
  simp

/-- A one-point configuration with prescribed spatial part and time. -/
def onePoint (s : Space) (t : ℝ) : Points 1 :=
  WithLp.toLp 2 fun _ => (WithLp.toLp 2 (Fin.snoc (α := fun _ => ℝ) s.ofLp t) : Spacetime)

/-! ### A Schwartz test with nonzero integral on `Points 1` -/

def bump : ContDiffBump (0 : Spacetime) := ⟨1, 2, one_pos, one_lt_two⟩

def bumpC : Spacetime → ℂ := fun y => ((bump y : ℝ) : ℂ)

theorem bumpC_smooth : ContDiff ℝ ∞ bumpC :=
  Complex.ofRealCLM.contDiff.comp bump.contDiff

theorem bumpC_support : HasCompactSupport bumpC :=
  bump.hasCompactSupport.comp_left Complex.ofReal_zero

def bumpTest : YangMills.TestFunction := bumpC_support.toSchwartzMap bumpC_smooth

theorem integral_bump_ne :
    (∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x) ≠ 0 := by
  have h1 : (fun x : Points 1 => Hierarchy.tensorTest (fun _ => bumpTest) x) =
      fun x => ((bump (x.ofLp 0) : ℝ) : ℂ) := by
    funext x
    simp only [Hierarchy.tensorTest, Fin.prod_univ_one]
    rfl
  rw [h1, integral_complex_ofReal]
  have hc : Continuous fun x : Points 1 => bump (x.ofLp 0) :=
    bump.continuous.comp (PiLp.continuous_apply _ _ 0)
  have hs : HasCompactSupport fun x : Points 1 => bump (x.ofLp 0) :=
    bump.hasCompactSupport.comp_homeomorph
      (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => Spacetime)).toHomeomorph
  have h0 : bump ((0 : Points 1).ofLp 0) ≠ 0 := by
    rw [show ((0 : Points 1).ofLp 0) = (0 : Spacetime) from rfl,
      bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
    exact one_ne_zero
  have hpos := hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hs
    (fun x => bump.nonneg) h0
  exact_mod_cast hpos.ne'

/-! ### Main statement -/

variable {g : GaugeGroup} {C : WilsonFamily g}

/-- The one-point word of the zero vector of grade `0`. -/
def zeroWord (T : Hierarchy C) : Fin 1 → T.Tag := fun _ => ⟨0, 0⟩

/-- Per-character `analytic`/`root`/`boundary` (the public shapes, specialized to the
one-point zero word) force the character's correlation there to vanish if it is constant. -/
theorem perPhase_zero_word (T : Hierarchy C) (i : T.Character)
    {H' : YangMills.HilbertSpace} (F : FieldSystem H' T.labels)
    (cont : (Fin 1 → ℂ) → (Fin 1 → Space) → ℂ)
    (analytic : ∀ sp, DifferentiableOn ℂ (fun z => cont z sp) (Hierarchy.orderedTube 1))
    (root : ∀ x : Points 1, StrictMono (fun k => time (x k)) →
      cont (Hierarchy.imaginaryTimes x) (Hierarchy.spatialPoints x) =
        T.correlation (some i) (zeroWord T) x)
    (boundary : ∀ height : Fin 1 → ℝ, StrictMono height →
      ∀ tests : Fin 1 → YangMills.TestFunction,
      Tendsto (fun r => ∫ x : Points 1, cont (Hierarchy.complexShift r height x)
        (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x) (𝓝[>] 0)
        (𝓝 (F.vacuumExpectation (fun k => T.toLabel (zeroWord T k).1 (zeroWord T k).2) tests)))
    (c : ℂ) (hc : ∀ x : Points 1, T.correlation (some i) (zeroWord T) x = c) : c = 0 := by
  have hsm1 : ∀ f : Fin 1 → ℝ, StrictMono f := fun f a b hab =>
    absurd hab (by rw [Subsingleton.elim a b]; exact lt_irrefl b)
  -- Step 1: the continuation is the constant `c` (identity theorem in one variable).
  have hconst : ∀ z sp, cont z sp = c := by
    intro z sp
    have hdiff : Differentiable ℂ (fun z : Fin 1 → ℂ => cont z sp) := by
      have h := analytic sp
      rw [orderedTube_one] at h
      exact differentiableOn_univ.mp h
    let G : ℂ → ℂ := fun w => cont (fun _ => w) sp
    have hG : Differentiable ℂ G :=
      hdiff.comp (differentiable_pi.2 fun _ => differentiable_id)
    have hGa : AnalyticOnNhd ℂ G Set.univ := fun w _ => hG.analyticAt w
    have hroot : ∀ t : ℝ, G ((t : ℂ) * Complex.I) = c := by
      intro t
      have ht : ∀ k, time ((onePoint (sp 0) t).ofLp k) = t := fun k => by
        first
        | (change Fin.snoc (α := fun _ => ℝ) (sp 0).ofLp t (Fin.last 3) = t
           exact Fin.snoc_last _ _)
        | (simp only [YangMills.time, onePoint, PiLp.toLp_apply]
           exact Fin.snoc_last _ _)
        | (unfold YangMills.time onePoint
           simp only [PiLp.toLp_apply, WithLp.ofLp_toLp]
           exact Fin.snoc_last _ _)
      have h1 : Hierarchy.imaginaryTimes (onePoint (sp 0) t) =
          fun _ => (t : ℂ) * Complex.I := by
        funext k
        simp only [Hierarchy.imaginaryTimes, ht]
      have h2 : Hierarchy.spatialPoints (onePoint (sp 0) t) = sp := by
        funext k
        rw [Subsingleton.elim k 0]
        simp [Hierarchy.spatialPoints, onePoint, YangMills.spatial, PiLp.toLp_apply]
      have := root (onePoint (sp 0) t) (hsm1 _)
      rw [h1, h2, hc] at this
      exact this
    have hu : Tendsto (fun n : ℕ => (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) atTop
        (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have h1 := ((Complex.continuous_ofReal.tendsto (0 : ℝ)).comp h0).mul_const Complex.I
        rw [Complex.ofReal_zero, zero_mul] at h1
        exact h1
      · exact mul_ne_zero (Complex.ofReal_ne_zero.2 (by positivity)) Complex.I_ne_zero
    have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), G w = c :=
      hu.frequently (Frequently.of_forall fun n => hroot (1 / ((n : ℝ) + 1)))
    have hGc : G = fun _ => c := hGa.eq_of_frequently_eq analyticOnNhd_const hfreq
    have hz : z = fun _ => z 0 := funext fun k => by rw [Subsingleton.elim k 0]
    rw [hz]
    exact congrFun hGc (z 0)
  -- Step 2: the boundary integral is `c * ∫ tensorTest`, but the vacuum expectation of a
  -- word with a zero label vanishes.
  have hlim := boundary (fun _ => 0) (hsm1 _) (fun _ => bumpTest)
  have hint : ∀ r : ℝ, (∫ x : Points 1, cont (Hierarchy.complexShift r (fun _ => 0) x)
      (Hierarchy.spatialPoints x) * Hierarchy.tensorTest (fun _ => bumpTest) x) =
      c * ∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x := by
    intro r
    simp_rw [hconst]
    exact integral_const_mul c _
  simp_rw [hint] at hlim
  have hzero : F.vacuumExpectation (fun k => T.toLabel (zeroWord T k).1 (zeroWord T k).2)
      (fun _ => bumpTest) = 0 :=
    vacuumExpectation_zero_label F _ _ 0 (by exact (T.toLabel 0).map_zero)
  rw [hzero] at hlim
  have heq : c * (∫ x : Points 1, Hierarchy.tensorTest (fun _ => bumpTest) x) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hlim
  exact (mul_eq_zero.mp heq).resolve_right integral_bump_ne

/-- The compiled reduction's second phase `2 * allZero - S`, on the one-point zero word, is
`2 * 1 - S(zeroWord)`; with `ZeroInvisible` (`S(zeroWord) = 0`) it is the constant `2`, so it
admits no per-character continuation/boundary data (repair R1). -/
theorem antiPhase_has_no_perPhase_data (T : Hierarchy C) (i : T.Character)
    (hanti : ∀ x : Points 1, T.correlation (some i) (zeroWord T) x =
      2 * 1 - T.correlation (some T.selected) (zeroWord T) x)
    (hZ : ∀ x : Points 1, T.correlation (some T.selected) (zeroWord T) x = 0)
    {H' : YangMills.HilbertSpace} (F : FieldSystem H' T.labels)
    (cont : (Fin 1 → ℂ) → (Fin 1 → Space) → ℂ)
    (analytic : ∀ sp, DifferentiableOn ℂ (fun z => cont z sp) (Hierarchy.orderedTube 1))
    (root : ∀ x : Points 1, StrictMono (fun k => time (x k)) →
      cont (Hierarchy.imaginaryTimes x) (Hierarchy.spatialPoints x) =
        T.correlation (some i) (zeroWord T) x)
    (boundary : ∀ height : Fin 1 → ℝ, StrictMono height →
      ∀ tests : Fin 1 → YangMills.TestFunction,
      Tendsto (fun r => ∫ x : Points 1, cont (Hierarchy.complexShift r height x)
        (Hierarchy.spatialPoints x) * Hierarchy.tensorTest tests x) (𝓝[>] 0)
        (𝓝 (F.vacuumExpectation (fun k => T.toLabel (zeroWord T k).1 (zeroWord T k).2) tests))) :
    False := by
  have h2 : ∀ x : Points 1, T.correlation (some i) (zeroWord T) x = 2 := fun x => by
    rw [hanti x, hZ x]; norm_num
  have := perPhase_zero_word T i F cont analytic root boundary 2 h2
  norm_num at this

end ReconBridgePerPhase

#print axioms ReconBridgePerPhase.perPhase_zero_word
#print axioms ReconBridgePerPhase.antiPhase_has_no_perPhase_data
