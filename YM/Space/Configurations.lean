import YM.Space.Index
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Positions, separated configurations and integrations

Common `E4` coordinates for Euclidean and Minkowski arguments (use `Proper`,
Lorentz etc. later for non-Euclidean operations). Euclidean `ℓ²` everywhere on
these *real vector spaces*. Distinguish sup/max metric `cubedist`. We keep the
full arity variables, not working on equal times by default.

Positions `Points n` also use the Euclidean norm; volume is Lebesgue volume
(`μ(dx₁...dxₙ)=∏ᵢ Lebesgue d⁴xᵢ`). We prove the adapters to ordinary tuples
for the ordered limits/spectral branches. Time last.
-/

set_option autoImplicit false
noncomputable section
namespace YM

open MeasureTheory Set WithLp Filter
open scoped Topology InnerProductSpace

abbrev E4 := EuclideanSpace ℝ Axis
abbrev Space3 := EuclideanSpace ℝ SpaceAxis

def time (x : E4) := x timeAxis
def spatial (x : E4) : Space3 := toLp 2 fun i => x i.castSucc
def position (x : Space3) (t : ℝ) : E4 := toLp 2 (Fin.snoc x.ofLp t)

@[simp] theorem time_position (x : Space3) (t : ℝ) : time (position x t) = t := by
  simp [time, position]
@[simp] theorem spatial_position (x : Space3) (t : ℝ) : spatial (position x t) = x := by
  apply PiLp.ext; intro i; simp [spatial, position]
@[simp] theorem position_eta (x : E4) : position (spatial x) (time x) = x := by
  apply PiLp.ext
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact time_position _ _
  · simp [spatial, position, time]

def basis (a : Axis) : E4 := EuclideanSpace.single a 1

@[simp] theorem basis_eq (i j : Axis) : basis i j = if j = i then 1 else 0 := by
  simp [basis, PiLp.single_apply, eq_comm]
@[simp] theorem basis_inner (i : Axis) (x : E4) : ⟪basis i,x⟫_ℝ = x i := by
  rw [basis, EuclideanSpace.inner_single_left]; simp
@[simp] theorem basis_norm (i : Axis) : ‖basis i‖ = 1 := by rw [basis]; simp

/-- The `L^∞` distance used in the cell bounds (includes time). -/
def cubedist (x y : E4) : ℝ := dist (ofLp x) (ofLp y)

@[fun_prop] theorem continuous_cubedist : Continuous fun p : E4 × E4 => cubedist p.1 p.2 := by
  unfold cubedist; fun_prop

abbrev Points (n : ℕ) := PiLp 2 (fun _ : Fin n => E4)

/-- Wrap a tuple. -/
def points {n : ℕ} (p : Fin n → E4) : Points n := toLp 2 p
@[simp] theorem points_apply {n : ℕ} (p : Fin n → E4) (i) : points p i = p i := rfl
@[simp] theorem points_eta {n : ℕ} (p : Points n) : points (ofLp p) = p := rfl

def conf (n : ℕ) : Set (Points n) := {x | Function.Injective x.ofLp}

/-- All coordinate projections separate. Do not confuse with `conf`. -/
def generic (n : ℕ) : Set (Points n) := {x | ∀ a : Axis, Function.Injective fun i => x i a}

/-- Stated as a predicate avoiding an `n ≥ 2` condition. Use with
`0 < r` for separated positions; with `r ≤ 1` for the capped bounds. -/
def spaced {n : ℕ} (r : ℝ) (x : Points n) : Prop := ∀ i j, i ≠ j → r ≤ cubedist (x i) (x j)

theorem generic_conf (n : ℕ) : generic n ⊆ conf n := by
  intro x h i j H
  exact h timeAxis (congr_arg (fun (u : E4) => u timeAxis) H)

theorem spaced_conf {n : ℕ} {r : ℝ} {x : Points n} (hr : 0 < r) (H : spaced r x) :
    x ∈ conf n := by
  intro i j h
  by_contra w
  have e : cubedist (x i) (x j) = 0 := by unfold cubedist; rw [h]; exact dist_self _
  exact hr.not_ge (e ▸ H i j w)

theorem conf_open (n : ℕ) : IsOpen (conf n) := by
  have he : conf n = ⋂ i : Fin n, ⋂ j : Fin n,
      ⋂ _ : i ≠ j, {x : Points n | x i ≠ x j} := by
    ext x
    simp only [mem_iInter, mem_setOf, conf]
    exact ⟨fun h i j hij ↦ h.ne hij, fun h i j hij ↦ by_contra fun w ↦ h i j w hij⟩
  rw [he]; refine isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite fun j ↦
    isOpen_iInter_of_finite fun _ ↦ isOpen_ne_fun ?_ ?_ <;> fun_prop

namespace Points

variable {n : ℕ}

def head (p : Points (n+1)) : E4 := p 0
def tail (p : Points (n+1)) : Points n := points fun i => p i.succ
def cons (x : E4) (p : Points n) := points (Fin.cons x (ofLp p))

def peel : Points (n+1) ≃ₗᵢ[ℝ] WithLp 2 (E4 × Points n) where
  toFun p := toLp 2 (head p, tail p)
  invFun p := cons p.fst p.snd
  left_inv p := by apply PiLp.ext; intro i; refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [head,cons,tail]
  right_inv p := by
    change toLp 2 (head _, tail _) = _
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [head,cons]
    · apply PiLp.ext
      simp [tail,cons]
  map_add' := by
    intro x y; apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [head]
    · exact PiLp.ext (fun _ => rfl)
  map_smul' := by
    intro c v; apply WithLp.ofLp_injective 2
    apply Prod.ext
    · simp [head]
    · exact PiLp.ext (fun _ => rfl)
  norm_map' p := by
    change ‖toLp 2 (head p, tail p)‖ = ‖p‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), WithLp.prod_norm_sq_eq_of_L2]
    change ‖head p‖^2 + ‖tail p‖^2 = _
    rw [PiLp.norm_sq_eq_of_L2 _ (tail p), PiLp.norm_sq_eq_of_L2 _ p,
      Fin.sum_univ_succ]
    rfl

@[simp] theorem peel_fst (x : Points (n+1)) : (peel x).fst = x 0 := rfl
@[simp] theorem peel_snd (x : Points (n+1)) (i) : (peel x).snd i = x i.succ := rfl

/-- Flatten spacetime vectors (including times) to Euclidean `4n` vectors. -/
def flatten : Points n ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Axis) where
  toFun p := toLp 2 fun i => p i.1 i.2
  invFun p := points fun i => toLp 2 fun a => p (i,a)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖toLp 2 fun p : Fin n × Axis => x p.1 p.2‖ = ‖x‖
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    simp only [PiLp.norm_sq_eq_of_L2, ← Finset.univ_product_univ, Finset.sum_product]

@[simp] theorem flatten_at (x : Points n) (i a) : flatten x (i,a) = x i a := rfl

theorem volume_nil : (volume : Measure (Points 0)) = Measure.dirac 0 := by
  have h := (flatten (n := 0)).symm.measurePreserving.map_eq
  rw [volume_euclideanSpace_eq_dirac, Measure.map_dirac, map_zero] at h
  exact h.symm

/-- Defuse the PiLp vs Pi convention for spacetime Lebesgue volume. -/
theorem volume_product (n : ℕ) :
    MeasurePreserving (ofLp : Points n → Fin n → E4) volume volume := by
  induction n with
  | zero =>
    constructor
    · exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 0 => E4)).continuous.measurable
    · rw [volume_nil, Measure.map_dirac, ofLp_zero, MeasureTheory.Measure.volume_pi_eq_dirac]
      apply congr_arg; exact Subsingleton.elim _ _
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => E4) 0
    have hp : MeasurePreserving
        (Prod.map id (ofLp : Points n → Fin n → E4)) volume volume :=
      (MeasurePreserving.id (volume : Measure E4)).prod ih
    have h : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hw := (h.symm).comp (hp.comp ((WithLp.volume_preserving_ofLp _ _).comp
      (LinearIsometryEquiv.measurePreserving (peel (n := n)))))
    have he : (⇑e.symm ∘ Prod.map (id : E4 → E4) ofLp ∘ ofLp ∘ (peel (n := n))) =
        (ofLp : Points (n+1) → Fin (n+1) → E4) := by
      funext p
      apply e.injective
      simp only [Function.comp_def, MeasurableEquiv.apply_symm_apply]
      apply Prod.ext
      · rfl
      · funext i
        simp [e, MeasurableEquiv.piFinSuccAbove, Prod.map, peel]
        rfl
    rw [he] at hw
    exact hw
end Points
end YM
