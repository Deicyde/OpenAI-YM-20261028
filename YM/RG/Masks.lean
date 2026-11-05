import YM.Gauge.Curvature
import Mathlib.Analysis.Calculus.ContDiff.Basic
import YM.Wilson.Law
import YM.Lattice.Support

/-!
A payload is computed from data within `supp`, with optional final flag queries
on `supp`. Do not use the shorter supports when integrating those flags.
Overlap/disjointness in the *evaluation* formula itself however is tested on the
original supports.

Regular payloads are specified BEFORE masking: to fix the norm and readout,
use a representative, not `Lᵖ` classes. We spell out the required differentiations
also via ordered left increments. Require differentiability where used; no
relying on junk `deriv`. The unmasked germ is carried as a single Borel function
(required to have been extended gauge invariantly). Off-domain values play no
role outside the derivatives and determining the dependence stencil; see ledger.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG
open Lattice Wilson
open MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology ContDiff

variable {n : Side} {G : Gauge}

def touched (p : Face (Per n)) : Finset (Site n) :=
  (visits p.1 (square p.2.val.1 p.2.val.2)).toFinset

/-- Every incident site flags if the chord is strictly above threshold.
K payloads still use the measured flags. -/
def flags (t : ℝ) (U : Config G n) : Support n := by
  classical
  exact Finset.univ.filter fun x => ∃ p, x ∈ touched p ∧ t < G.chord (faceValue U p)

theorem flags_spec (t : ℝ) (U : Config G n) (x) :
    x ∈ flags t U ↔ ∃ p, x ∈ touched p ∧ t < G.chord (faceValue U p) := by simp [flags]

def Healthy (t : ℝ) (X : Support n) (U : Config G n) := Disjoint X (flags t U)

@[simp] theorem gauge_flags (t : ℝ) (U : Config G n) (k : Site n → G.El) :
    flags t (gauge k U) = flags t U := by
  ext; simp only [flags_spec, face_gauge, Gauge.chord_conj]

theorem flags_open (x : Site n) (t : ℝ) : IsOpen {U : Config G n | x ∈ flags t U} := by
  simp only [flags_spec, setOf_exists]; apply isOpen_iUnion; intro p
  by_cases h : x ∈ touched p
  · simp only [h, true_and, faceValue]; exact isOpen_lt continuous_const (by fun_prop)
  simp [h]

theorem healthy_closed (t : ℝ) (X : Support n) : IsClosed {U : Config G n | Healthy t X U} := by
  have e : {U : Config G n | Healthy t X U} = (⋃ x : X, {U | x.val ∈ flags t U})ᶜ := by
    ext; simp [Healthy, Finset.disjoint_left]
  rw [e]; exact (isOpen_iUnion fun _ => flags_open ..).isClosed_compl

theorem flags_measurable_eq (t : ℝ) (X : Support n) :
    MeasurableSet {U : Config G n | flags t U = X} := by
  rw [show {U : Config G n | flags t U = X} = ⋂ x : Site n,
      if x ∈ X then {U | x ∈ flags t U} else {U | x ∈ flags t U}ᶜ by
    ext U
    simp only [mem_setOf_eq, Finset.ext_iff, mem_iInter]
    apply forall_congr'; intro i; split <;> simp [*]]
  refine MeasurableSet.iInter fun i ↦ ?_
  split <;> first | apply MeasurableSet.compl; exact (flags_open ..).measurableSet | exact (flags_open ..).measurableSet

variable {X : Type*}

def masked [Zero X] (t : ℝ) (P : Support n) (F : Config G n → X) : Config G n → X := by
  classical
  exact Set.indicator {U | Healthy t P U} F

@[simp] theorem masked_eq [Zero X] (t : ℝ) (P : Support n) (F : Config G n → X) (U : Config G n)
    (h : Healthy t P U) : masked t P F U = F U := Set.indicator_of_mem h F

@[simp] theorem masked_ne [Zero X] (t : ℝ) (P : Support n) (F : Config G n → X) (U : Config G n)
    (h : ¬ Healthy t P U) : masked t P F U = 0 := Set.indicator_of_notMem h F

@[fun_prop] theorem masked_measurable [MeasurableSpace X] [Zero X] (t : ℝ) (P : Support n)
    (F : Config G n → X) (h : Measurable F) : Measurable (masked t P F) :=
  h.indicator (healthy_closed t P).measurableSet

def UsesFinal {X : Sort*} (t : ℝ) (P : Support n) (F : Config G n → X) :=
  ∀ U V, Agrees P U V → P ∩ flags t U = P ∩ flags t V → F U = F V

/-- Tested flags force one more layer of physical reads before pushing. -/
def inspected (P : Support n) : Support n := P ∪ (Finset.univ.biUnion fun p : Face (Per n) =>
  if Disjoint P (touched p) then ∅ else touched p)

theorem flags_agree (t : ℝ) (U V : Config G n) (P : Support n) (h : Agrees (inspected P) U V) :
    P ∩ flags t U = P ∩ flags t V := by
  have he (x : Site n) (hx : x ∈ P) (p : Face (Per n)) (hp : x ∈ touched p) :
      faceValue U p = faceValue V p := by
    apply travel_local _ _ U V
    apply agrees_mono h
    intro y hy
    have hg : ¬ Disjoint P (touched p) := fun H => Finset.disjoint_left.mp H hx hp
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ p, ?_⟩)
    rw [if_neg hg]; exact List.mem_toFinset.mpr hy
  ext x; simp only [Finset.mem_inter, flags_spec]
  by_cases hx : x ∈ P
  · simp only [hx, true_and]
    apply exists_congr; intro p
    by_cases hp : x ∈ touched p <;> simp [*, he x hx p]
  · simp [hx]

theorem UsesFinal.allReads (t : ℝ) (P : Support n) {X : Type*} (F : Config G n → X)
    (h : UsesFinal t P F) : LocalOn (inspected P) F := fun U V h' =>
  h _ _ (agrees_mono h' fun _ hx ↦ Finset.mem_union_left _ hx) (flags_agree t U V P h')

/-- Real or complex regular value extensions use LEFT-link increments,
in normalized colors. For finite directions use the component norms; total
vector space topology is the default product. -/
abbrev Directions (G : Gauge) (n : Side) := Edge (Site n) → G.Color

def increment (U : Config G n) (A : Directions G n) : Config G n :=
  fun e => G.lieExp (A e) * U e

def leftDerivs [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F : Config G n → X) : List (Directions G n) → Config G n → X
  | [], U => F U
  | A::l, U => deriv (fun t : ℝ => leftDerivs F l (increment U (t • A))) 0

structure BudgetPoint where
  power : ℕ
  order : ℕ
  supportExponent : ℝ
  B : ℕ
  threshold : ℝ
  power_ge : 2 ≤ power
  order_ge : 6 ≤ order
  exponent_pos : 0 < supportExponent
  B_pos : 0 < B
  threshold_pos : 0 < threshold
  threshold_le : threshold ≤ 1

namespace BudgetPoint
variable (p : BudgetPoint)

def dirBound (o : Site n) (A : Directions G n) : Prop := ∀ e : Edge (Site n),
    ‖A e‖ ≤ p.threshold * (1+(separation e.1 o : ℝ))^p.power

def mass (P : Support n) (c : ℝ) : ℝ := Real.exp (p.supportExponent * coverNumber p.B P) * c

theorem loMass (P : Support n) (c : ℝ) (hc : 0 ≤ c) : c ≤ p.mass P c := by
  have he : 0 ≤ p.supportExponent * coverNumber p.B P := mul_nonneg p.exponent_pos.le (by positivity)
  exact le_mul_of_one_le_left hc (Real.one_le_exp he)

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- Germ carried by `F`; use that germ also at equality. Require global
cylindrical Borel and gauge-invariant representative. -/
structure Regular (P : Support n) (F : Config G n → X) : Prop where
  sites : LocalOn P F
  borel : Measurable F
  symmetry : GaugeInvariant F
  smooth (U) : Healthy p.threshold P U →
    ContDiffAt ℝ (p.order : ℕ∞) (fun v => F (increment U v)) 0
  hasDerivs (U) : Healthy p.threshold P U → ∀ A l, l.length < p.order →
    HasDerivAt (fun t : ℝ => leftDerivs F l (increment U (t • A))) (leftDerivs F (A::l) U) 0


def supBounds (o : Site n) (P : Support n) (F : Config G n → X) (c : ℝ) : Prop :=
    0 ≤ c ∧ ∀ U, Healthy p.threshold P U → ∀ l, List.length l ≤ p.order →
      (∀ A ∈ l, p.dirBound o A) → ‖leftDerivs F l U‖ ≤ c
end BudgetPoint
end YM.RG
