import YM.OS.Caps

/-!
# Heat operators on actual GNS spaces

Axes beyond temporal used in rotation argument. Needed endpoint facts
proved without spectral assertions. Semigroup parameter NNReal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter Analysis Word
open scoped Topology BigOperators InnerProductSpace NNReal ComplexOrder ComplexConjugate
variable {G : Gauge} {L : Register G} {S : Table L} {a : Axis} (X : Schwinger S a)

abbrev Voice (L : Register G) (a : Axis) := Future L a →₀ ℂ

def timed (t : ℝ≥0) : Voice L a →ₗ[ℂ] X.H := Finsupp.linearCombination ℂ (fun x => X.plant (travel x t))
def offAxis (u : Cross a) : Voice L a →ₗ[ℂ] X.H := Finsupp.linearCombination ℂ (fun x => X.plant (over x u))

lemma symmetrical (h : S.Homogeneous) (t u) (p q : Voice L a) :
    inner ℂ (timed X t p) (timed X u q) = inner ℂ (X.stems p) (timed X (u+t) q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single x c =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,inner_add_right,hf,hg]
    | single y d =>
      simp only [timed,Kernel.Gram.stems,Finsupp.linearCombination_single, inner_smul_left, inner_smul_right,
        X.measure, sym_time h a x (travel y u), advances]

lemma bothside (h : S.Homogeneous) (u) (p q : Voice L a) : inner ℂ (offAxis X u p) (offAxis X u q) =
    inner ℂ (X.stems p) (X.stems q) := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add,inner_add_left,hf,hg]
  | single x c =>
    induction q using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg => simp only [map_add,inner_add_right,hf,hg]
    | single y d =>
      simp only [offAxis,Kernel.Gram.stems,Finsupp.linearCombination_single,inner_smul_left,inner_smul_right,X.measure,
        sym_space h a]

lemma sq_key (v : X.H) : ‖v‖^2 = ‖inner ℂ v v‖ := by rw [inner_self_eq_norm_sq_to_K]; simp

lemma safe (u : Cross a) (H : S.Hierarchy) (p : Voice L a) : ‖offAxis X u p‖ = ‖X.stems p‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq_key X,sq_key X, bothside X H.translations]

lemma enough (H : S.Hierarchy) (p : Voice L a) : ∃ R : ℝ, ∀ t, ‖timed X t p‖ ≤ R := by
  induction p using Finsupp.induction_linear with
  | zero => exact ⟨0,fun _ => by simp⟩
  | add f g hf hg =>
    obtain ⟨A,hA⟩ := hf; obtain ⟨B,hB⟩ := hg
    refine ⟨A+B,fun t => ?_⟩
    rw [map_add]; exact (norm_add_le ..).trans (add_le_add (hA t) (hB t))
  | single w c =>
    obtain ⟨B,hB⟩ := (correl H a w w).2
    have he (t : ℝ≥0) : ‖X.plant (travel w t)‖^2 ≤ B := by
      rw [sq_key X,X.measure, sym_time H.translations, advances]
      exact hB _ (by simp)
    refine ⟨‖c‖ * √B,fun t => ?_⟩
    rw [timed, Finsupp.linearCombination_single,norm_smul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact ((Real.le_sqrt (norm_nonneg _) (le_trans (sq_nonneg _) (he t))).mpr (he t))

/-- Doubling bounds. Sup trick: take sup over all t, so no large-power calculation. -/
lemma contract (H : S.Hierarchy) (t) (p : Voice L a) : ‖timed X t p‖ ≤ ‖X.stems p‖ := by
  let d i := ‖timed X i p‖
  have ht : BddAbove (Set.range d) := by
    obtain ⟨A,hA⟩ := enough X H p; exact ⟨A,by rintro _ ⟨y,rfl⟩; exact hA y⟩
  let c := ⨆ i : ℝ≥0, d i
  have he i : d i ≤ c := le_ciSup ht _
  have hp : 0 ≤ d t := norm_nonneg _
  have hh (i) : d i ^ 2 ≤ ‖X.stems p‖ * c := by
    change ‖timed X i p‖^2 ≤ _
    rw [sq_key X, symmetrical X H.translations]
    exact (norm_inner_le_norm ..).trans (mul_le_mul_of_nonneg_left (he _) (norm_nonneg _))
  let A := ‖X.stems p‖*c
  have hA : 0 ≤ A := le_trans (sq_nonneg _) (hh t)
  have h₀ := hp.trans (he t)
  have hw : c ≤ √A := ciSup_le fun i => (Real.le_sqrt (norm_nonneg (timed X i p)) hA).mpr (hh i)
  apply (he t).trans
  have hq := sq_le_sq₀ h₀ (Real.sqrt_nonneg A) |>.2 hw
  rw [Real.sq_sqrt hA] at hq
  dsimp only [A] at hq
  nlinarith [norm_nonneg (X.stems p)]

/-!
Reusable abstraction. No OpNorm topology on translations.
-/
structure Semigroup (H : Hilbert) (a : Axis) where
  E (t : ℝ≥0) : H.Op
  U (s : Cross a) : H.Op
  eZero : E 0=ContinuousLinearMap.id ℂ _
  time t s : E (t+s)=(E t).comp (E s)
  shrinks t : ‖E t‖ ≤ 1
  sym t : (E t).adjoint = E t
  uZero : U 0=ContinuousLinearMap.id ℂ _
  space t s : U (t+s)=(U t).comp (U s)
  unitary t v : ‖U t v‖=‖v‖
  independent t s : (E t).comp (U s)=(U s).comp (E t)
  continuousE v : Continuous (fun t => E t v)
  continuousU v : Continuous (fun t => U t v)

lemma strong {Y : Type*} [TopologicalSpace Y] {D : Hilbert} {f : Y → X.H.space →L[ℂ] D.space}
    (hp : ∀ x, ‖f x‖ ≤ 1) (h : ∀ i, Continuous fun x => f x (X.plant i)) : ∀ v : X.H, Continuous fun x => f x v := by
  have he (v : Voice L a) : Continuous fun x => f x (X.stems v) := by
    induction v using Finsupp.induction_linear with
    | zero => simp only [map_zero]; exact continuous_const
    | add i j hi hj => simp_rw [map_add]; exact hi.add hj
    | single i c => simp_rw [Kernel.Gram.stems,Finsupp.linearCombination_single,map_smul]
                    exact continuous_const.smul (h i)
  intro v
  refine continuous_iff_continuousAt.mpr fun x => Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g,hg,H⟩ := Metric.mem_closure_iff.mp (X.whole v) (ε/4) (by positivity)
  obtain ⟨u,rfl⟩ := hg
  have hw (y) : dist (f y v) (f y (X.stems u)) < ε/4 := by
    rw [dist_eq_norm, ← map_sub]
    exact lt_of_le_of_lt ((f y).le_opNorm _ |>.trans (mul_le_of_le_one_left (norm_nonneg _) (hp y)))
      (by simpa [dist_eq_norm] using H)
  filter_upwards [Metric.tendsto_nhds.mp (show ContinuousAt (fun x => f x (X.stems u)) x from (he u).continuousAt).tendsto (ε/4) (by positivity)] with y hy
  have hu := dist_triangle (f y v) (f y (X.stems u)) (f x (X.stems u))
  have hg := dist_triangle (f y v) (f x (X.stems u)) (f x v)
  change dist (f y v) (f x v)<ε
  have h₁ := hw y
  have h₂ := hw x
  rw [dist_comm] at h₂
  linarith
end YM.OS
