import YM.Next.MULTISOURCE.Adjoining
import YM.Next.MULTISOURCE.Decal


/-!
# Scalar stability gate to RG and Reference producers

Small-perturbation estimate at the VACUUM step. This time *no marker
ring and no mixed jets*. Uses ordinary scalar complex E/K perturbations.
Keeps the actual choices of unmarked activities, clips, masking,
prior, push and path; not asking to rock the history or beta branch over
this domain! Analytic-diagram style: each output slot can be polynomial in
the amplitudes, with the projected-support reading rule. (There's no bound on
the degree, can use countably many.) Need a POINTWISE unmarked estimate
at small perturbations. Pointwise even in amplitudes on that domain;
not requiring sup vs series exchanges, limits of norms on any stencil,
or an estimate of any Taylor coefficients, simultaneous or otherwise.

It is stronger in what it requires on the unmarked step
than just a marked susceptibility estimate, but a way to attack that
remaining analytic estimate by exposing needs at RAdvances/RPaper.

E.g.
an unmarked scalar block lemma accommodating even complex variations of
incoming E/K with the *same retained history at zero*, with numerical
addresses retaining data read from input, might be a natural byproduct
to try for in unnormalized sector/reclosure estimates.

Not claiming
it's proved or implied by the unmarked estimates in E.

Need also
compatibility with the first derivative in the RMakes port on THIS family,
one stroke at a time.

Baseline histories committed at S.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Lattice Wilson Filter Finset MeasureTheory Marker Desk
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {n : Side} {G : Gauge} {I : Type*}

-- Zero-stroke unit dictionary for ordinary estimates.
-- a stroke costs at ONE anchor, knows standard support array. The producer
-- can also work with more general E as long as it gives this receipt.
structure Scratch (P : BudgetPoint) (D : Pulse G n) (o : Site n) (k κ : ℝ) (W : ℕ → Support n) : Prop where
  nonneg : 0 ≤ k
  owned : ∃ (H : ℕ → Config G n → ℂ) (f : ℕ → ℝ), (∀ i, o∈W i ∧ P.Regular (W i) (H i) ∧ P.supBounds o (W i) (H i) (f i)) ∧
      SumBudget (fun i => P.mass (W i) (f i)) k ∧ ∀ U,D.1 U=∑' i,masked P.threshold (W i) (H i) U
  forced : ∃ f : Pack n → ℝ, (∑ i,P.mass i.zone (f i)) ≤ κ*k ∧ ∀ i, Legible P i (D.2 i) ∧
      (D.2 i ≠ 0 → o∈i.zone) ∧ 0 ≤ f i ∧ ∀ U, ‖D.2 i U‖ ≤ f i

section
variable (P : Rep G n)

def baseJoint (U : Config G n) (M : Pack n → ℂ) :=
    (Real.exp (P.exponent U):ℂ)*(∑ i∈ Pack.clears (flags P.p.threshold U), ∏ x∈i,(incumbent P U x + M x))

def progeny (U : Config G n) (E : ℂ) (M : Pack n → ℂ) := Complex.exp E * baseJoint P U M
end

variable [Fintype I]

def perturbs (P : Rep G n) (D : I → Pulse G n) (z : I→ℂ) (U : Config G n) := progeny P U
    (∑ i, z i * (D i).1 U) (fun j => ∑ i,z i*(D i).2 j U)

structure Reservoir (P : Rep G n) (I : Type*) where
  support : ℕ→Support n
  k : ℕ → Pack n
  /-- global unit (only along reference axes, affine-order; higher orders can leave constants in H) -/
  pay : I→ℂ
  D : ℕ → Config G n → Wave I
  K : ℕ → Config G n → Wave I

namespace Reservoir
open MvPolynomial
variable {P : Rep G n} (T : Reservoir P I)

def listed {X : Type*} (f : X → Wave I) := ∃ V : Finset (Grade I), ∀ U, (f U).support ⊆ V

def keeps (i : ℕ) (U : Config G n) := masked P.p.threshold (T.support i) (T.D i) U

def records (q : Pack n) (i : ℕ) (U : Config G n) := if q=T.k i then T.K i U else 0

def taste (q : Grade I) : Pulse G n :=
    (fun U => coeff q (staves T.pay)+∑' j, coeff q (T.keeps j U), fun i U => ∑' j, coeff q (T.records i j U))

structure Tested (κ : ℝ) (A : Set (I→ℂ)) : Prop where
  nonempty i : (T.support i).Nonempty
  polya i : listed (T.D i)
  polyb i : listed (T.K i)
  warm (i) U : coeff 0 (T.D i U)=0
  temp (i) U : coeff 0 (T.K i U)=0
  smooth (z : I→ℂ) : z∈A → ∀ i,P.p.Regular (T.support i) (eval z ∘ T.D i)
  bulk (z : I→ℂ) : z∈A → ∃ f : ℕ→ℝ,
      (∀ i, 0 ≤ f i ∧ ∀ x∈T.support i,P.p.supBounds x (T.support i) (eval z ∘ T.D i) (f i)) ∧
      ∀ x : Site n,SumBudget (fun i => if x ∈ T.support i then burn P.p 2 (T.support i)*f i else 0) 1
  reads (z : I→ℂ) : z∈A → ∀ i,Legible P.p (T.k i) (eval z ∘ T.K i)
  titles (z : I→ℂ) : z∈A → ∃ f : ℕ→ℝ, (∀ i, 0 ≤ f i ∧ ∀ U,‖eval z (T.K i U)‖ ≤ f i) ∧
      ∀ x : Site n,SumBudget (fun i => if x∈(T.k i).zone then burn P.p 2 (T.k i).zone*f i else 0) κ

def tasteE (z : I→ℂ) (U : Config G n) := eval z (staves T.pay)+∑' j, eval z (T.keeps j U)
def tasteK (q : Pack n) (z : I→ℂ) (U : Config G n) := ∑' j, eval z (T.records q j U)

def signal (z : I→ℂ) (U : Config G n) := progeny P U (T.tasteE z U) (fun q => T.tasteK q z U)

def sleepy (A : Set (I→ℂ)) (x : I) (p : Wave I) := ∀ z∈A,∀ y∈A,(∀ i, i≠x → z i=y i) → eval z p=eval y p

structure Shelved (A : Set (I→ℂ)) (R : I→Support n → Prop) : Prop where
  trust y i U : ¬ R y (T.support i) → sleepy A y (T.D i U)
  rent y i U : ¬ R y (T.k i).zone → sleepy A y (T.K i U)
end Reservoir

/-! Perturbation domains. -/
section
variable {V : Type} [Fintype V]

def allot (o : V→Site n) (k : V→ℝ) (ρ : ℝ) : Set (V→ℂ) := {z | ∀ x : Site n,
    (∑ i, if o i=x then ‖z i‖*k i else 0) ≤ ρ}

variable (C : Family G) (d j : ℕ)

def Stability := ∀ N p, j < N →
    let A := C.path.levels
    let S := A.clock.op j p
    let P := C.path.rep N p j
    let Q := C.path.rep N p (j+1)
    ∀ (V : Type) [Fintype V] [DecidableEq V] (D : V → Pulse G (C.side (j+1) p))
      (k : V→ℝ) (o : V→Site (C.side j p)) (ref : V → Option (C.label d))
      (X : V → ℕ → Support (C.side (j+1) p)),
      Set.InjOn o {i | (ref i).isSome} →
      (∀ i,ref i=none → Scratch Q.p (D i) (S.ratio.embed (o i)) (k i) (money A (j+1)) (X i)) →
      (∀ i v, ref i=some v → D i=Single.one C N v (S.ratio.embed (o i)) ∧ k i=Single.tariff C N p (j+1) v ∧
        Credit Q.p 0 (money A (j+1)) {S.ratio.embed (o i)} (D i) (k i)) →
      let R := allot o k (neighboring C j)⁻¹
      ∃ T : Reservoir P V,T.Tested (money A j) R ∧
        T.Shelved R (fun i Y => if ref i=none then
          (∃ u, (X i u).image S.ratio.parent ⊆ Y) ∨ (∃ q : Pack _,(D i).2 q ≠ 0 ∧ q.zone.image S.ratio.parent ⊆ Y)
          else o i ∈ Y) ∧
        (∀ i, ref i=none → T.pay i=0) ∧
        (∀ i v, ref i=some v → (touch C d j:ℂ) • T.taste (Desk.power {i})=Single.one C N v (o i)) ∧
        ∀ z ∈ R,T.signal z=S.push Q.beta (perturbs Q D z)

def Stable := ∀ᶠ j : ℕ in atTop, Stability C d j
end
end YM.Multi
