import YM.RG.ActivityBounds
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import YM.Wilson.Symmetry

/-!
# Transport rows and canonical atoms

Body of eq:ved.

Paths are on the cover, not bounded by the torus *distance*.

All-face orientation channels from  applied to the WHOLE exponent terms
using the pulled configurations.

These definitions specify the normalized
kinetic read (`metric_zero`, loop jets, affine test on E).

They do not require
the particular Fourier strip estimates by which one hopes to construct the
arrays.

They *do* require symmetry, width, iteration and remainder budgets in
the history.

Existential; no uniqueness of fitted representations as functions
is claimed or used.

Cf.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice Wilson MeasureTheory Filter Set
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

/-- One based transported curvature slot, cover units. -/
structure Slot where
  walk : Walk
  plaq : PlaqAxes

namespace Slot
variable (a : Slot)

def offset : Cover := stop 0 a.walk

def stencil : Finset Cover := (visits 0 a.walk).toFinset ∪
  (visits a.offset (square a.plaq.val.1 a.plaq.val.2)).toFinset

def length := a.walk.length + 4

def eval {G : Gauge} (U : CoverConfig G) : G.Color :=
  G.adjoint (travel U 0 a.walk) (G.curvature (faceValue U (a.offset,a.plaq)))

def atSite {G : Gauge} {n : Side} (U : Config G n) (x : Site n) : G.Color :=
  a.eval (expandAt x U)

theorem eval_norm {G : Gauge} (U : CoverConfig G) : ‖a.eval U‖ ≤ 2 := by
  unfold eval
  rw [G.norm_adjoint]
  exact (G.curvature_norm _).trans (G.chord_le_two _)

@[fun_prop] theorem cont {G : Gauge} : Continuous (a.eval (G := G)) := by
  unfold eval Gauge.adjoint
  have hm (F) (hc : Continuous (F : CoverConfig G → G.Mat)) :
      Continuous fun U => G.projectColor (F U) := G.projectColor.continuous_of_finiteDimensional.comp hc
  refine hm _ ?_
  have ha := show Continuous fun U : CoverConfig G => G.colorMat (G.curvature (faceValue U (a.offset,a.plaq))) from
    G.colorMat.continuous_of_finiteDimensional.comp (G.continuous_curvature.comp (continuous_travel _ _))
  unfold Gauge.conjugate; fun_prop

theorem covered {G : Gauge} : LocalOn a.stencil (a.eval (G := G)) := by
  intro U V h
  rw [eval, eval]
  have hh : travel U 0 a.walk = travel V 0 a.walk :=
    travel_local _ _ _ _ fun e he hm ↦ h e (Finset.mem_union_left _ (List.mem_toFinset.mpr he))
      (Finset.mem_union_left _ (List.mem_toFinset.mpr hm))
  have ht : faceValue U (a.offset,a.plaq) = faceValue V (a.offset,a.plaq) :=
    travel_local _ _ _ _ fun e he hm ↦ h e (Finset.mem_union_right _ (List.mem_toFinset.mpr he))
      (Finset.mem_union_right _ (List.mem_toFinset.mpr hm))
  rw [hh,ht]
end Slot

structure Atom (G : Gauge) (k : ℕ) where
  leg : Fin k → Slot
  coeff : (Fin k → G.ColorIndex) → ℝ

namespace Atom
variable {G : Gauge} {k : ℕ} {n : Side} (a : Atom G k)

def length := ∑ i, (a.leg i).length

def magnitude := ∑ b, |a.coeff b|

def budget (σ : ℝ) := a.magnitude * Real.exp (σ * a.length)

def poly (x : Fin k → G.Color) := ∑ b, a.coeff b * ∏ i, x i (b i)

def Invariant : Prop := ∀ u x, a.poly (fun i => G.adjoint u (x i)) = a.poly x

def stencil : Finset Cover := insert 0 (Finset.univ.biUnion fun i => (a.leg i).stencil)

def footprint (x : Site n) := a.stencil.image fun p => wrap n p + x

def unmasked (U : Config G n) (x : Site n) := a.poly fun i => (a.leg i).atSite U x

def placed (p : BudgetPoint) (U : Config G n) (x : Site n) :=
  masked p.threshold (a.footprint x) (fun V => a.unmasked V x) U

theorem lower_budget (σ : ℝ) (h : 0 < σ) : a.magnitude ≤ a.budget σ :=
  le_mul_of_one_le_right (by unfold magnitude; positivity) (Real.one_le_exp (by positivity))

@[fun_prop] theorem unmasked_cont (x : Site n) : Continuous fun U => a.unmasked U x := by
  unfold unmasked poly Slot.atSite expandAt; fun_prop

theorem unmasked_bound (U : Config G n) (x : Site n) : |a.unmasked U x| ≤ a.magnitude * 2^k := by
  have hh (i j) : |(a.leg i).atSite U x j| ≤ 2 := calc
    _ = |inner ℝ (EuclideanSpace.basisFun G.ColorIndex ℝ j) ((a.leg i).atSite U x)| := by simp only [EuclideanSpace.basisFun_inner]
    _ ≤ _ := (abs_real_inner_le_norm _ _).trans <| by
      rw [OrthonormalBasis.norm_eq_one, one_mul]; exact Slot.eval_norm ..
  unfold unmasked poly magnitude
  rw [Finset.sum_mul]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum; intro i _
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  convert Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) (fun k _ ↦ hh k (i k)) using 1
  simp

lemma placed_bound (p : BudgetPoint) (U : Config G n) (x : Site n) :
    |a.placed p U x| ≤ a.magnitude * 2^k := by
  unfold placed
  by_cases h : Healthy p.threshold (a.footprint x) U
  · rw [masked_eq _ _ _ _ h]; exact a.unmasked_bound ..
  rw [masked_ne _ _ _ _ h]; unfold magnitude; simp only [abs_zero]; positivity
end Atom

/-- Parameters for clipping per stage. -/
structure Clip where
  direct : ℝ
  linear : ℝ
  relaxation : ℝ
  quadratic_pos : 0 < direct
  tail_pos : 0 < linear
  kink : linear < direct / 16
  radius_pos : 0 < relaxation

/-- Data from  (denotational arrays on the cover).
`ℓ^U` always uses actual Ad along the paths. -/
structure PathData (G : Gauge) where
  row : PlaqAxes → ℕ → (ℝ × Slot)
  loop : ℕ → Atom G 2
  cubic : ℕ → Atom G 3
  quartic : ℕ → Atom G 4
namespace PathData
variable {n : Side} {G : Gauge} (R : PathData G)

def symbol0 (i j : PlaqAxes) :=
  ∑' k : ℕ, if (R.row i k).2.plaq = j then (R.row i k).1 else 0

def metric_zero (c : Clip) : Prop := ∀ i j : PlaqAxes,
    (if i=j then c.direct else 0) + (∑ k, R.symbol0 k i * R.symbol0 k j) = if i=j then 1 else 0

def loop_coeff (a : Fin 2 → PlaqAxes) (x : Fin 2 → G.ColorIndex) (k : ℕ) :=
    if (fun i => ((R.loop k).leg i).plaq) = a then (R.loop k).coeff x else 0

def loop_jets : Prop := ∀ i x, (∑' k, R.loop_coeff i x k) = 0 ∧ ∀ l : Axis,
    (∑' k, R.loop_coeff i x k *
      ((((R.loop k).leg 1).offset l - ((R.loop k).leg 0).offset l : ℤ) : ℝ)) = 0

/-- Weight clauses. Include actual `Summable` requirements explicitly also for
any unguarded moments in the normalization. -/
structure Bounds (c : Clip) (σ C Λ : ℝ) : Prop where
  width : 0 < σ
  rows (p : PlaqAxes) : SumBudget (fun i ↦ |(R.row p i).1| * Real.exp (σ * (R.row p i).2.length)) C
  two : SumBudget (fun i ↦ (R.loop i).budget σ) Λ
  three : SumBudget (fun i ↦ (R.cubic i).budget σ) C
  four : SumBudget (fun i ↦ (R.quartic i).budget σ) C
  invariant (i : ℕ) : (R.loop i).Invariant ∧ (R.cubic i).Invariant ∧ (R.quartic i).Invariant
  symTerms (p q : PlaqAxes) : Summable fun k => if (R.row p k).2.plaq = q then (R.row p k).1 else 0
  metric : R.metric_zero c
  loopTerms (i x) : Summable (R.loop_coeff i x) ∧ ∀ l : Axis,
    Summable (fun k => R.loop_coeff i x k *
      ((((R.loop k).leg 1).offset l - ((R.loop k).leg 0).offset l : ℤ) : ℝ))
  loop_normal : R.loop_jets

def ellTerms (p : Face (Per n)) (i : ℕ) (U : Config G n) :=
    (R.row p.2 i).1 • ((R.row p.2 i).2.atSite U p.1)

def ell (U : Config G n) (p : Face (Per n)) := ∑' i, R.ellTerms p i U

theorem ell_dominated {σ C Λ : ℝ} {c : Clip} (h : R.Bounds c σ C Λ) (p : Face (Per n)) :
    Dominated (R.ellTerms p) := by
  obtain ⟨-,H,-⟩ := h.rows p.2
  refine ⟨_, H.mul_right 2, ?_⟩
  intro i U
  rw [ellTerms, norm_smul, Real.norm_eq_abs]
  apply mul_le_mul ?_ (Slot.eval_norm ..) (norm_nonneg _) (by positivity)
  apply le_mul_of_one_le_right (by positivity)
  exact Real.one_le_exp (mul_nonneg h.width.le (by positivity))

theorem ell_meas (p : Face (Per n)) (c : Clip) (σ C Λ : ℝ) (_ : R.Bounds c σ C Λ) :
    Measurable fun U => R.ell U p := by
  unfold ell
  apply Measurable.tsum
  intro i
  refine Continuous.measurable ?_
  unfold ellTerms Slot.atSite expandAt; fun_prop

def kept (c : Clip) (t : ℝ) (x : Site n) (U : Config G n) : Prop :=
    ∀ p : Face (Per n), G.chord (faceValue U p) ≤ t * Real.exp (separation x p.1 / c.relaxation)

lemma kept_closed (c : Clip) (t : ℝ) (x : Site n) : IsClosed {U : Config G n | kept c t x U} := by
  simp only [kept, setOf_forall]
  apply isClosed_iInter; intro p
  exact isClosed_le (by unfold faceValue; fun_prop) continuous_const

def clipped (c : Clip) (t : ℝ) (s : ℝ) : ℝ :=
    if s ≤ t then c.direct * s^2/2 else c.linear*t*s

def baseTerm (c : Clip) (p : BudgetPoint) (U : Config G n) (x : Face (Per n)) : ℝ := by
  classical
  exact clipped c p.threshold (G.chord (faceValue U x)) +
    (if kept c p.threshold x.1 U then ‖R.ell U x‖^2/2 else 0)

def atomSeries {k : ℕ} (F : ℕ → Atom G k) (p : BudgetPoint) (U : Config G n) (x : Site n) :=
  ∑' i, (F i).placed p U x

lemma atom_dominated {σ C : ℝ} {k : ℕ} (F : ℕ → Atom G k) (p : BudgetPoint) (x : Site n)
    (hp : 0 < σ) (hb : SumBudget (fun i ↦ (F i).budget σ) C) :
    Dominated fun i U => (F i).placed p U x :=
  ⟨_, hb.2.1.mul_right (2^k), fun i U ↦ ((F i).placed_bound p U x).trans <|
    mul_le_mul_of_nonneg_right ((F i).lower_budget σ hp) (by positivity)⟩

/-- In a given orientation channel. -/
def principal (c : Clip) (p : BudgetPoint) (β : ℝ) (U : Config G n) : ℝ :=
  β * ((∑ f, R.baseTerm c p U f) + ∑ x : Site n,
      (atomSeries R.cubic p U x + atomSeries R.quartic p U x)) + ∑ x, atomSeries R.loop p U x

/-- Average over signed channels of the WHOLE action. -/
def inChannels (c : Clip) (p : BudgetPoint) (β : ℝ) (U : Config G n) :=
  (Fintype.card Signed : ℝ)⁻¹ * ∑ s : Signed, R.principal c p β (pull s 0 U)
end PathData
end YM.RG
