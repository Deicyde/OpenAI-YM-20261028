import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import YM.Maxwell.Shell

set_option warningAsError false

/-!
# Algebra diagnostics: homogeneous Maxwell solutions

Bianchi and Maxwell divergence both imposed, ordinary Euclidean gradients (not
Minkowski / not a barred convention).

Recall `Tensor.coeff` uses Taylor
coefficients, *dividing by the factorial*.

Independent of existence/selection
of any interacting family.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Maxwell Analysis Tensor
open scoped Topology ContDiff BigOperators

section calculus
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f g : E4 → F} {x : E4}

lemma grad_smul (hf : ContDiffAt ℝ ∞ f x) (a : Axis) (t : ℝ) :
    grad a (t • f) x = t • grad a f x := by
  unfold grad D; rw [fderiv_const_smul (hf.differentiableAt (by simp))]; rfl

lemma grad_plus (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (a : Axis) :
    grad a (f+g) x = grad a f x + grad a g x := by
  unfold grad D; rw [fderiv_add (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]; rfl

lemma grad_neg_f (a : Axis) : grad a (-f) x = -grad a f x := by
  unfold grad D; rw [fderiv_neg]; rfl

lemma grad_sum_f {ι : Type*} (s : Finset ι) {f : ι → E4 → F} (hf : ∀ i ∈ s, ContDiffAt ℝ ∞ (f i) x) (a : Axis) :
    grad a (∑ i ∈ s, f i) x = ∑ i ∈ s, grad a (f i) x := by
  classical
  have he : (∑ i ∈ s, f i) = fun y => ∑ i ∈ s, f i y := funext fun _ => Finset.sum_apply ..
  rw [he]
  unfold grad D
  rw [fderiv_fun_sum (fun i hi => (hf i hi).differentiableAt (by simp)),sum_apply]

lemma grad_exchange (hf : ContDiffAt ℝ ∞ f x) (a b : Axis) :
    grad a (grad b f) x = grad b (grad a f) x :=
  grad_comm (hf.of_le (show (↑(2:ℕ) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) _ _

lemma grad_smooth_at (hf : ContDiffAt ℝ ∞ f x) (a : Axis) :
    ContDiffAt ℝ ∞ (grad a f) x := grad_smooth _ hf (by simp)

/-- Germ Laplacian, dimension four. -/
def lap (f : E4 → F) (x : E4) : F := ∑ a : Axis, grad a (grad a f) x

/-- Maxwell on an open set implies harmonicity there. -/
lemma wave_lap {A : Maxwell.Field F} {U : Set E4} (hu : IsOpen U) (h : WaveOn U A)
    (hx : x ∈ U) (i m : Axis) : lap (A i m) x = 0 := by
  have hb := hu.mem_nhds hx
  have hd (a b c : Axis) := grad_smooth_at (h.smooth b c x hx) a
  have he (a : Axis) : grad a (grad a (A i m)) x + grad a (grad i (A m a)) x +
      grad a (grad m (A a i)) x = 0 := by
    have hc : (grad a (A i m) + grad i (A m a) + grad m (A a i)) =ᶠ[𝓝 x] (0 : E4 → F) := by
      filter_upwards [hb] with y hy; exact h.cycle a i m y hy
    have ht : grad a (grad a (A i m) + grad i (A m a) + grad m (A a i)) x = 0 :=
      (GermD _ hc).trans (by simp [D])
    have hs : ContDiffAt ℝ ∞ (grad a (A i m) + grad i (A m a)) x := (hd _ _ _).add (hd _ _ _)
    rwa [grad_plus hs (hd _ _ _),grad_plus (hd _ _ _) (hd _ _ _)] at ht
  have hz (b c : Axis) : ∑ a : Axis, grad a (grad b (A a c)) x = 0 := by
    have ht : (∑ a : Axis, grad a (A a c)) =ᶠ[𝓝 x] (0 : E4 → F) := by
      filter_upwards [hb] with y hy; rw [Finset.sum_apply]; exact h.divergence c y hy
    simp_rw [fun a => grad_exchange (h.smooth a c x hx) a b]
    rw [← grad_sum_f _ (a := b) (f := fun a => grad a (A a c)) (fun _ _ => hd _ _ _)]
    exact (GermD _ ht).trans (by simp [D])
  have hn (a : Axis) : grad a (grad i (A m a)) x = -grad a (grad i (A a m)) x := by
    have hg : grad i (A m a) =ᶠ[𝓝 x] -grad i (A a m) := by
      filter_upwards [hb] with y hy
      have hw : A m a =ᶠ[𝓝 y] - A a m := by
        filter_upwards [hu.mem_nhds hy] with z hh; exact h.form m a z hh
      exact (GermD _ hw).trans (grad_neg_f i)
    exact (GermD _ hg).trans (grad_neg_f a)
  have ht := Finset.sum_eq_zero (s := (Finset.univ : Finset Axis)) (fun a _ => he a)
  simp_rw [Finset.sum_add_distrib, hn,Finset.sum_neg_distrib,hz,neg_zero,add_zero] at ht
  exact ht

lemma wave_grad {A : Maxwell.Field F} {U : Set E4} (hu : IsOpen U) (h : WaveOn U A) (a : Axis) :
    WaveOn U (fun i m => grad a (A i m)) := by
  refine ⟨fun i m x hx => grad_smooth_at (h.smooth i m x hx) a,?_,?_,?_⟩
  · intro i m x hx
    have he : A i m =ᶠ[𝓝 x] - A m i := by
      filter_upwards [hu.mem_nhds hx] with z hz; exact h.form i m z hz
    exact (GermD _ he).trans (grad_neg_f a)
  · intro b c i x hx
    rw [grad_exchange (h.smooth c i x hx),grad_exchange (h.smooth i b x hx) c a,grad_exchange (h.smooth b c x hx) i a]
    have hd (k u v) := grad_smooth_at (h.smooth u v x hx) k
    have ht : grad b (A c i) + grad c (A i b) + grad i (A b c) =ᶠ[𝓝 x] (0 : E4 → F) := by
      filter_upwards [hu.mem_nhds hx] with z hz; exact h.cycle b c i z hz
    have hs : ContDiffAt ℝ ∞ (grad b (A c i) + grad c (A i b)) x := (hd _ _ _).add (hd _ _ _)
    rw [← grad_plus (hd _ _ _) (hd _ _ _),← grad_plus hs (hd _ _ _)]
    exact (GermD _ ht).trans (by simp [D])
  intro b x hx
  have hd i := grad_smooth_at (h.smooth i b x hx) i
  have ht : (∑ i : Axis, grad i (A i b)) =ᶠ[𝓝 x] (0 : E4 → F) := by
    filter_upwards [hu.mem_nhds hx] with z hz; rw [Finset.sum_apply]; exact h.divergence b z hz
  simp_rw [fun i => grad_exchange (h.smooth i b x hx) i a]
  rw [← grad_sum_f (f := fun i => grad i (A i b)) _ (fun _ _ => hd _)]
  exact (GermD _ ht).trans (by simp [D])
end calculus

abbrev Sol (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ℕ) := ↥(onShell F j)

namespace Sol
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {j : ℕ}

def field (S : Sol F j) : Maxwell.Field F := fun a b => diagonal (S.val a b)

theorem closed (S : Sol F j) : ClosedJet S.val := S.property.1

theorem wave (S : Sol F j) : WaveOn univ S.field := by
  refine ⟨fun i m _ _ => (diag_smooth _ _).contDiffAt, fun i m x _ => ?_,fun i m a x _ => S.closed.closed i m a x,fun i x _ => S.property.2 i x⟩
  unfold field; nth_rw 1 [S.closed.antisymmetric i m]; rfl

theorem smooth (S : Sol F j) (a b : Axis) (x : E4) : ContDiffAt ℝ ∞ (S.field a b) x := S.wave.smooth a b x (mem_univ _)
theorem harmonic (S : Sol F j) (a b : Axis) (x : E4) : lap (S.field a b) x = 0 := wave_lap isOpen_univ S.wave (mem_univ x) a b

theorem val_freeze (S : Sol F (j+1)) (a i m : Axis) :
    grad a (S.field i m) = ((j+1 : ℕ) : ℝ) • diagonal ((S.val i m).curryLeft (basis a)) := by
  funext x
  change fderiv ℝ (diagonal (S.val i m)) x (basis a) = _
  rw [differential_diagonal _ (S.closed.coeffSym i m)]
  simp only [Pi.smul_apply,Nat.cast_smul_eq_nsmul]
  rfl

/-- Fix one direction, still on the same shell of order one lower. -/
def freeze (S : Sol F (j+1)) (a : Axis) : Sol F j :=
  ⟨fun i m => (S.val i m).curryLeft (basis a), by
    have hd := wave_grad isOpen_univ S.wave a
    have hv : (↑(j+1:ℕ):ℝ) ≠ 0 := by positivity
    have he (c i m x) : grad c (grad a (S.field i m)) x = ((j+1:ℕ):ℝ) •
        grad c (diagonal ((S.val i m).curryLeft (basis a))) x := by
      rw [S.val_freeze]; exact grad_smul (diag_smooth _ _|>.contDiffAt) c _
    constructor
    · constructor
      · intro i m; exact freeze_sym _ (S.closed.coeffSym _ _) _
      · intro i m
        nth_rw 1 [S.closed.antisymmetric i m]; rfl
      intro i m c x
      have ht := hd.cycle i m c x (mem_univ x)
      simp_rw [he,← smul_add] at ht
      exact (smul_eq_zero.mp ht).resolve_left hv
    intro i x
    have ht := hd.divergence i x (mem_univ x)
    simp_rw [he, ← Finset.smul_sum] at ht
    exact (smul_eq_zero.mp ht).resolve_left hv ⟩

theorem grad_field (S : Sol F (j+1)) (a i m : Axis) :
    grad a (S.field i m) = ((j+1 : ℕ) : ℝ) • ((freeze S a).field i m) := S.val_freeze a i m

theorem freeze_trace (S : Sol F (j+1)) (i m : Axis) (z : E4) :
    ∑ a : Axis, grad a ((freeze S a).field i m) z = 0 := by
  have he := S.harmonic i m z
  unfold lap at he
  have ht (a) : grad a (grad a (S.field i m)) z =
      ((j+1:ℕ):ℝ) • grad a ((freeze S a).field i m) z := by
    rw [S.grad_field]; exact grad_smul ((freeze S a).smooth i m z) a _
  simp_rw [ht,← Finset.smul_sum] at he
  exact (smul_eq_zero.mp he).resolve_left (by positivity)
end Sol
end YM.Extra.FD
