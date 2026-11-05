import YM.Hilbert.Kolmogorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Real

/-!
# Shared PVMs and spectral values

Explicitly strong additivity, projection multiplication, identity.
No postulated existence. Later ports consume scalarized dominating positive
measure for pairings, no vector-measure integration dependence.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spectral
open MeasureTheory Filter Complex Function Set
open scoped Topology BigOperators ContDiff InnerProductSpace

variable {H : Hilbert} {X : Type*} [MeasurableSpace X]
structure PVM (H : Hilbert) (X : Type*) [MeasurableSpace X] where
  region : Set X → H.Op
  none : region ∅ = 0
  all : region univ = ContinuousLinearMap.id ℂ _
  joins {s t} : MeasurableSet s → MeasurableSet t → (region s).comp (region t) = region (s∩t)
  real {s} : MeasurableSet s → (region s).adjoint = region s
  unites (s : ℕ → Set X) (hs : ∀ i, MeasurableSet (s i)) (h : Pairwise (Disjoint on s)) (x : H) :
    HasSum (fun i => region (s i) x) (region (⋃ i, s i) x)
  diagonal : H → Measure X
  finite (x : H) : IsFiniteMeasure (diagonal x)
  at_pair {s} (h : MeasurableSet s) (x : H) : ↑((diagonal x).real s) = inner ℂ x (region s x)

namespace PVM
attribute [instance] finite
variable (P : PVM H X)

lemma idempotent {s} (h : MeasurableSet s) (x : H) : P.region s (P.region s x)=P.region s x := by
  rw [← ContinuousLinearMap.comp_apply,P.joins h h, Set.inter_self]

lemma same {s} (h : MeasurableSet s) (x : H) : (P.diagonal x).real s = ‖P.region s x‖^2 := by
  apply Complex.ofReal_injective
  rw [P.at_pair h,Complex.ofReal_pow]
  suffices he : inner ℂ x (P.region s x) = inner ℂ (P.region s x) (P.region s x) from he.trans (inner_self_eq_norm_sq_to_K ..)
  conv_rhs => lhs; arg 1; rw [← P.real h]
  rw [ContinuousLinearMap.adjoint_inner_left,P.idempotent h]

lemma null_pair {s} (h : MeasurableSet s) (x : H) : P.diagonal x s=0 ↔ P.region s x=0 := by
  rw [← measureReal_eq_zero_iff (measure_ne_top (P.diagonal x) s), P.same h]; simp
end PVM

/-- Strongly continuous unitary translations (linear-in-SECOND orbit). -/
structure Orbit (H : Hilbert) (X : Type*) [AddCommGroup X] [TopologicalSpace X] where
  translation (a : X) : H.Op
  origin : translation 0=ContinuousLinearMap.id ℂ _
  sends (a b) : (translation a).comp (translation b)=translation (a+b)
  unitary (a : X) (v) : ‖translation a v‖=‖v‖
  moves (v : H) : Continuous (fun a => translation a v)

end YM.Spectral
