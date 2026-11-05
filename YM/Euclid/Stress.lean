import YM.Euclid.Words
import YM.Euclid.Union

/-!
# Tensor laws, stress and charge interfaces

at arbitrary center. Fluxes read finite quotients, no
near-diagonal contact term (density differentiates the shell test). This
also supplies centered/angular, or unaveraged versions as needed in bootstrapping
rotation jobs. `O(4)` is the same real matrix convention as raw H on positions;
include generators as HasDerivAt of each orbit (for real evolution parameter).
No conclusion of integration from matrix bracket without the actual action.
-/
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter MeasureTheory Analysis
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
variable {G : Gauge} {L : Register G} {S : Table L}

namespace Table
structure Rotation (S : Table L) where
  act (d : ℕ) : Ortho → (S.Field d ≃ₗ[ℂ] S.Field d)
  lie (d : ℕ) : Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)

namespace Rotation
variable (R : S.Rotation)

def label (K : Ortho) (v : S.Tag) : S.Tag := ⟨v.1,R.act v.1 K v.2⟩

structure Laws (P : DiffPlan S) (H : S.RealSpin) : Prop where
  spin d s : Continuous (fun K => R.act d K s)
  fixes d s : R.act d 1 s = s
  group d g k s : R.act d (g*k) s = R.act d g (R.act d k s)
  signed d (s : Signed) v : R.act d s.ortho v = S.mirror H d s v
  real d s v : S.conj H d (R.act d s v) = R.act d s (S.conj H d v)
  identity d s : R.act d s (S.unit d) = S.unit d
  filtered d e (h : d ≤ e) s v : R.act e s (P.rise h v) = P.rise h (R.act d s v)
  vector d s a v : R.act (d+1) s ((P.deriv d a) v) = ∑ i : Axis, ((s.val i a : ℝ) : ℂ) •
    P.deriv d i (R.act d s v)
  infinitesimal (d : ℕ) (g : Ortho.Skew) (v : S.Field d) :
    HasDerivAt (fun t => R.act d (Ortho.oneParameter g t) v) (R.lie d g v) (0 : ℝ)

/-- Quotient covariance, with `T.respects S`. Heterogeneous and any positions
in Conf. Implies transported-plane RP with the Euclidean Basic/RP laws. -/
def Oriented (T : Table L) :=
  ∀ n (v : Fin n → S.Tag), ∀ x ∈ conf n, ∀ K : Ortho,
    S.useAt T (Points.move K x) (R.label K ∘ v) = S.useAt T x v

-- orbit derivative is also continuous linear in v (here finite-dimensional); explicit vanish on units.
theorem kills {P H} (h : R.Laws P H) (d : ℕ) (a : Ortho.Skew) : R.lie d a (S.unit d)=0 := by
  have he := h.infinitesimal d a (S.unit d)
  simp_rw [h.identity] at he
  exact he.unique (hasDerivAt_const ..)
end Rotation

abbrev Stress (S : Table L) := Axis → Axis → S.Field 4

structure Conserved (P : DiffPlan S) (H : S.RealSpin) (J : S.Stress) : Prop where
  symmetric : ∀ a b, J a b = J b a
  real : ∀ a b, S.conj H 4 (J a b) = J a b
  divergence : ∀ b, ∑ a : Axis, P.deriv 4 a (J a b) = 0

def Tensorial (R : S.Rotation) (J : S.Stress) :=
  ∀ K a b, R.act 4 K (J a b) = ∑ i : Axis, ∑ j : Axis,
    (((K.val i a * K.val j b : ℝ) : ℂ)) • J i j

def RawTensor (H : S.RealSpin) (J : S.Stress) :=
  ∀ k a b, S.mirror H 4 k (J a b) = ∑ i : Axis, ∑ j : Axis,
    (((k.matrix i a * k.matrix j b : ℝ) : ℂ)) • J i j

def Window {n : ℕ} (x : Points (n+1)) (χ : E4 → ℝ) := ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
  χ =ᶠ[𝓝 (x 0)] (fun _ => 1) ∧ ∀ i : Fin n, x i.succ ∉ tsupport χ

section
variable (T : Table L) (J : S.Stress) {d n : ℕ}

/-- translation shell, no basis dependence. -/
def shellGrad (χ : E4 → ℝ) (b : Axis) (x : Points (n+1)) (q : Fin n → S.Tag) (B : S.Field d) :=
  - ∑ a : Axis, ∫ y : E4, ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
    S.useAt T (Points.cons y x) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q))

/-- angular shell about the center (first slot of x). -/
def shellSpin (χ : E4 → ℝ) (g : Ortho.Skew) (x : Points (n+1)) (q : Fin n → S.Tag) (B : S.Field d) :=
  - ∑ a : Axis, ∑ b : Axis, ∫ y : E4, ((Analysis.D (basis a) χ y * M4.move g.val (y - x 0) b : ℝ) : ℂ) *
    S.useAt T (Points.cons y x) (Fin.cons ⟨4,J a b⟩ (Fin.cons ⟨d,B⟩ q))

/-- Applies also to any translated center/test shell. Assumes kernels are smooth
on Conf for use. Does not test contact term at B point. -/
structure StressLaws (Y : ∀ d : ℕ, Axis → S.Field d →ₗ[ℂ] S.Field (d+1))
    (A : ∀ d : ℕ, Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d)) : Prop where
  translation {n : ℕ} {x} (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag) {χ : E4 → ℝ} (w : Window x χ)
    (b : Axis) (d : ℕ) (B : S.Field d) : shellGrad T J χ b x q B =
      S.useAt T x (Fin.cons ⟨d+1,Y d b B⟩ q)
  rotation {n : ℕ} {x} (hx : x ∈ conf (n+1)) (q : Fin n → S.Tag) {χ : E4 → ℝ} (w : Window x χ)
    (g : Ortho.Skew) (d : ℕ) (B : S.Field d) : shellSpin T J χ g x q B =
      S.useAt T x (Fin.cons ⟨d,A d g B⟩ q)
end
end Table
end YM
