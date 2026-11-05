import YM.Fields.Star
import YM.Spectral.Frequencies
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Fields on the common invariant word domain, target 

No new label system, operators descend on `S.Union`, evaluated via the W
from (strict-order continued) selected phase. Poincare representation on
same Hilbert space. Test adjoints as sesquilinear identities & PROVE usual
operator inclusion. Positivity follows. Spectrum includes PVM+support, not
assuming spectral theorem.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Boundary
open Function Filter Set MeasureTheory Spectral Analysis Complex Mink
open scoped Topology BigOperators ComplexOrder InnerProductSpace

variable {G : Gauge} {L : Register G} {S : Table L}

structure Fields (S : Table L) where
  H : Hilbert
  domain : Submodule ℂ H
  omega : domain
  field : S.Union →ₗ[ℂ] Test4 →ₗ[ℂ] (domain →ₗ[ℂ] domain)

namespace Fields
variable (F : Fields S)

def edits (v : Letter S) := F.field v.1 v.2

def evaluates : Sentence S → F.domain
  | [] => F.omega
  | v::w => F.edits v (evaluates w)

def vector (v : Sentence S) := (F.evaluates v).val

def vacuum := F.omega.val

structure Total : Prop where
  norm : ‖F.vacuum‖ = 1
  everywhere : Dense (F.domain : Set F.H)
  cyclic : F.domain = Submodule.span ℂ (Set.range F.vector)
  temperate (x : S.Union) (v : F.domain) : Continuous (fun f => (F.field x f v).val)

def sharpPair (J : StarOp S) := ∀ (x : S.Union) (f : Test4) (a b : F.domain),
  inner ℂ (F.field x f a).val b.val = inner ℂ a.val (F.field (J x) (Probe.bar f) b).val

def denselyDefined (x : S.Union) (f : Test4) : F.H →ₗ.[ℂ] F.H :=
  ⟨F.domain,F.domain.subtype.comp (F.field x f)⟩

theorem really (J : StarOp S) (h : F.Total) (hp : F.sharpPair J) (x : S.Union) (f : Test4) :
    F.denselyDefined (J x) (Probe.bar f) ≤ (F.denselyDefined x f).adjoint :=
  LinearPMap.IsFormalAdjoint.le_adjoint h.everywhere (fun a b => hp x f a b)

/-- no null: for every nonzero class there's ψ and f seeing it. -/
def notLost := ∀ p : S.Union, p ≠ 0 → ∃ f : Test4, F.field p f ≠ 0

def realizes (W : Surface S) := ∀ b : Sentence S, inner ℂ F.vacuum (F.vector b)=W.expect b

lemma general (W : Surface S) (t : F.realizes W) (J : StarOp S) (h : F.sharpPair J) (b c : Sentence S) :
    inner ℂ (F.vector b) (F.vector c) = W.kernel J b c := by
  induction b generalizing c with
  | nil => exact t c
  | cons v b ih =>
    change inner ℂ (F.field v.1 v.2 _).val (F.evaluates c).val = _
    rw [h v.1 v.2]
    change inner ℂ (F.vector b) (F.vector (Letter.op J v :: c)) = _
    rw [ih]; simp [Surface.kernel,Sentence.rev]

theorem hilbertNonnegative {X : Type*} (D : Hilbert) (p : X → D) : NNKernel (fun i j => inner ℂ (p i) (p j)) := by
  apply NNKernel.criterion
  · intro i j; exact inner_conj_symm ..
  intro n x c
  let v := ∑ i, c i • p (x i)
  have hp : inner ℂ v v = ∑ i, ∑ j, star (c i)*inner ℂ (p (x i)) (p (x j))*c j := by
    unfold v; rw [sum_inner]; simp only [inner_sum,inner_smul_left,inner_smul_right, Complex.star_def,mul_comm]
  rw [← hp,inner_self_eq_norm_sq_to_K]
  positivity

theorem sees (W : Surface S) (t : F.realizes W) (J : StarOp S) (h : F.sharpPair J) : W.wordsPositive J := by
  rw [Surface.wordsPositive,show W.kernel J = _ from funext fun i => funext fun j => (F.general W t J h i j).symm]
  apply hilbertNonnegative

def causal (f g : Test4) := ∀ x ∈ tsupport f, ∀ y ∈ tsupport g, x-y ∈ Mink.spacelike

def commutes := ∀ (x y : S.Union) (f g : Test4), causal f g → ∀ p : F.domain,
    F.field x f (F.field y g p) = F.field y g (F.field x f p)
end Fields

structure Action (H : Hilbert) where
  V : Poincare → (H →L[ℂ] H)
  one : V 1=ContinuousLinearMap.id ℂ _
  mult (g k : Poincare) : V (g*k)=(V g).comp (V k)
  usual (g : Poincare) (x : H) : ‖V g x‖=‖x‖
  strong (x : H) : Continuous (fun g => V g x)

namespace Action
variable {H : Hilbert} (V : Action H)
def orbit : Orbit H E4 where
  translation p := V.V (Poincare.translation p)
  origin := V.one
  sends x y := by rw [Poincare.overE,V.mult]
  unitary _ := V.usual _
  moves x := (V.strong x).comp Poincare.continuousE

lemma goes (p : Poincare) (x : H) : V.V p⁻¹ (V.V p x)=x := by rw [← ContinuousLinearMap.comp_apply,← V.mult,inv_mul_cancel,V.one];rfl
end Action

structure Symmetries (X : Spins S) {F : Fields S} (V : Action F.H) : Prop where
  domain (p : Poincare) : Set.MapsTo (V.V p) (F.domain : Set F.H) F.domain
  vacuum (p : Poincare) : V.V p F.vacuum=F.vacuum
  covariance (p : Poincare) (x : S.Union) (f : Test4) (a : F.domain) : V.V p (F.field x f a).val =
    (F.field (X.rail p.Λ x) (Joint.push p f) (⟨V.V p a.val, domain p a.property⟩ : F.domain)).val

structure Wightman (S : Table L) where
  spin : Spins S
  operators : Fields S
  J : StarOp S
  action : Action operators.H
  momentum : PVM operators.H E4

structure Wightman.Realizes {W : Surface S} (R : Wightman S) (V : S.Rotation) (h : S.RealSpin) : Prop where
  induced : starRead R.J h
  letters : R.spin.Descends V h
  total : R.operators.Total
  adj : R.operators.sharpPair R.J
  meets : R.operators.realizes W
  localPairs : R.operators.commutes
  faithful : R.operators.notLost
  covariance : Symmetries R.spin R.action
  spectral : R.action.orbit.Spectrum R.momentum
  forward : R.momentum.region Mink.coneᶜ = 0
  unique (v : R.operators.H) : (∀ x, R.action.orbit.translation x v=v) → ∃ z : ℂ, z • R.operators.vacuum=v

end YM.Boundary
