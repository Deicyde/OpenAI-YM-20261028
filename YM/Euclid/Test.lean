import YM.Space.Configurations
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Test against *all* compact smooth separated tests

Ambient `TestFunction` on `conf`, Lebesgue on Points n. Boundary uses joint Schwartz maps instead.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open MeasureTheory Set Function TopologicalSpace Filter
open scoped Topology ContDiff

def patch (n : ℕ) : Opens (Points n) := ⟨conf n,conf_open _⟩
abbrev Test (n : ℕ) := TestFunction (patch n) ℂ ⊤
abbrev RealTest (n : ℕ) := TestFunction (patch n) ℝ ⊤

namespace Test
variable {n : ℕ}

@[simp] theorem vanishes (f : Test n) {x : Points n} (h : x ∉ conf n) : f x = 0 :=
  by_contra fun w => h (f.tsupport_subset (subset_closure w))

/-- Complex linear convention (not sesquilinear). -/
def applyTo (f : Test n) (K : Points n → ℂ) := ∫ x : Points n, f x * K x

theorem smearing (f : Test n) {K} (H : ContinuousOn K (conf n)) :
    Integrable (fun x => f x * K x) := by
  have hu : HasCompactSupport ((f : Points n → ℂ) * K) := HasCompactSupport.mul_right f.hasCompactSupport
  refine Continuous.integrable_of_hasCompactSupport ?_ hu
  refine continuous_iff_continuousAt.mpr fun x => ?_
  by_cases h : x ∈ conf n
  · exact f.continuous.continuousAt.mul ((H x h).continuousAt ((conf_open _).mem_nhds h))
  have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport f := isOpen_compl_iff.mpr (isClosed_tsupport _)
    |>.mem_nhds (show x ∈ (tsupport f)ᶜ from fun w => h (f.tsupport_subset w))
  refine continuousAt_const.congr (?_ : (fun _ => (0:ℂ)) =ᶠ[𝓝 x] fun a => f a*K a)
  filter_upwards [he] with y hy
  rw [show f y = 0 from by_contra fun w ↦ hy (subset_closure w), zero_mul]

theorem schwartz (f : Test n) : ∃ g : SchwartzMap (Points n) ℂ, (f : Points n → ℂ) = g :=
  ⟨HasCompactSupport.toSchwartzMap f.hasCompactSupport f.contDiff,rfl⟩

theorem apply_eq (f : Test n) {K P} (H : EqOn K P (conf n)) : f.applyTo K = f.applyTo P := by
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ conf n
  · exact congr_arg (fun y => f x * y) (H hx)
  simp [hx]

/-- Null via all such tests equals null at separated points for continuous kernels. -/
theorem weak_null {K : Points n → ℂ} (HK : ContinuousOn K (conf n)) :
    (∀ f : Test n, f.applyTo K = 0) ↔ EqOn K 0 (conf n) := by
  constructor
  · intro h
    have he := (conf_open _).ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (HK.locallyIntegrableOn (conf_open _).measurableSet) (fun g hg hg' H => ?_)
    · exact Measure.eqOn_open_of_ae_eq ((ae_restrict_iff' (conf_open _).measurableSet).mpr he)
        (conf_open _) HK continuousOn_const
    let f : Points n → ℂ := Complex.ofRealCLM ∘ g
    have hu : tsupport f = tsupport g := by
      unfold tsupport
      rw [show support f = support g by ext; simp [f]]
    let p : Test n := ⟨f, Complex.ofRealCLM.contDiff.comp hg,
      by rw [HasCompactSupport, hu]; exact hg', hu ▸ H⟩
    rw [← h p]; apply integral_congr_ae
    exact Eventually.of_forall fun x => Complex.real_smul
  intro H f; rw [apply_eq f H]; simp [applyTo]

/-- Equality on compact smooth separated tests already determines continuous kernels. -/
theorem unique_kernel {K P : Points n → ℂ} (hK : ContinuousOn K (conf n)) (hP : ContinuousOn P (conf n)) :
    (∀ f : Test n, f.applyTo K = f.applyTo P) ↔ EqOn K P (conf n) := by
  constructor
  · intro H
    have h : EqOn (K-P) 0 (conf n) := (weak_null (hK.sub hP)).1 fun f => by
      unfold applyTo; simp_rw [Pi.sub_apply, mul_sub]; rw [integral_sub (f.smearing hK) (f.smearing hP)]
      exact sub_eq_zero.mpr (H f)
    exact fun _ hx => sub_eq_zero.mp (h hx)
  exact fun h f => apply_eq f h
end Test
end YM
