import YM.Pert.Lattice.Bundles
import Mathlib.Analysis.Calculus.ImplicitContDiff
/-! Numerical Taylor polynomials for finite-regulator readings and the local implicit function for square position tests. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Position
open Set Function Filter
open scoped Topology ContDiff BigOperators

section curve
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
/-- Taylor data as a numerical polynomial *just for computing jets*. No Taylor-series convergence needed. -/
def curve (x : ℕ→E) (m : ℕ) (t : ℝ) : E := ∑ i ∈ Finset.range (m+1), t^i • x i
lemma curve_diff (x : ℕ→E) (m : ℕ) : ContDiff ℝ ω (curve x m) := by unfold curve; exact ContDiff.sum (fun i _ => (contDiff_id.pow i).smul contDiff_const)
lemma curve_zero (x : ℕ→E) (m : ℕ) : curve x m 0 = x 0 := by simp [curve,show ∀ i : ℕ, (0:ℝ)^i=if i=0 then 1 else 0 from fun i=> by by_cases h:i=0 <;> first | (exact Eq.trans (zero_pow h) (by rw [if_neg h])) | exact h.symm ▸ Eq.symm (if_pos rfl),ite_smul]
end curve

section analytic
variable {A C Z V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup C] [NormedSpace ℝ C] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Tested datum `x` of all determining equations, `z` for a reported functional of the frame. `n` is derivative order and `m` input truncation order. -/
def readJet (φ : A→V) (m n : ℕ) (W : C×V → Z) (x : ℕ→A) (z : ℕ→C) := iteratedDeriv n (fun t : ℝ => W (curve z m t, φ (curve x m t))) 0
end analytic

section patches
variable {A V Y : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A] [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

structure Reports (f : A×V→Y) (x : A) (y : V) (φ : A → V) : Prop where
  fixes : φ x = y
  diff : ContDiffAt ℝ ω φ x
  curves : ∀ᶠ z in 𝓝 x, f (z,φ z)=f (x,y)
  strict : ∀ᶠ v in 𝓝 (x,y), f v=f (x,y) ↔ φ v.1=v.2
lemma Reports.of_square {f : A × V→Y} {x : A} {y : V} (hf : ContDiffAt ℝ ω f (x,y)) (hL : ((fderiv ℝ f (x,y)).comp (ContinuousLinearMap.inr ℝ A V)).IsInvertible) :
    ∃ φ : A → V, Reports f x y φ := ⟨hf.implicitFunction (by simp) hL, hf.implicitFunction_apply_self .., ContDiffAt.contDiffAt_implicitFunction hf (by simp) hL,hf.eventually_apply_implicitFunction .., hf.eventually_apply_eq_iff_implicitFunction ..⟩
lemma Reports.deletion {f : A×V→Y} {x : ℕ→A} {y} {φ} (h : Reports f (x 0) y φ) {I : Type*} {l : Filter I} {D : ℕ→I→A} (hD : Tendsto (D 0) l (𝓝 (x 0))) (m n : ℕ) : ∀ᶠ k in l, readJet φ m n f (fun i=>D i k) (fun i=>D i k) = iteratedDeriv n (fun _ : ℝ=>(f (x 0,y))) (0:ℝ) := by
  have hep (i : I) := curve_diff (fun j => D j i) m |>.continuous.tendsto (0:ℝ)
  simp only [curve_zero] at hep
  have h' : ∀ᶠ z in 𝓝 (x 0), ∀ᶠ v in 𝓝 z, f (v,φ v) = f (x 0,y) := eventually_eventually_nhds.mpr h.curves
  exact (hD.eventually h').mono (fun k hk => Filter.EventuallyEq.iteratedDeriv_eq n (hep k |>.eventually hk))
end patches
end YM.Pert.Position
