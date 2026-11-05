import YM.Analysis.SmoothJets

set_option warningAsError false

/-!
# Finite price questions on a stationary graph

Envelope calculus: 3rd and 4th REAL derivatives, no stationary graph
solving on the exterior inputs: Critical and its flat derivative solution
give the entire rule. Will apply to the genuine pair `(B,relative tree chart)`
of the authenticated Step. No suppressions or finite norms assumed on the
formal variables.
-/
set_option autoImplicit false
noncomputable section

namespace YM.AnalyticNext.CalendarScene.Jets

open Filter Function Matrix
open Analysis (D)
open scoped Topology BigOperators ContDiff
variable {E F U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup U] [NormedSpace ℝ U]



abbrev J2 (f : F → U) (x i j : F) := iteratedFDeriv ℝ 2 f x ![i,j]
abbrev J3 (f : F → U) (x i j k : F) := iteratedFDeriv ℝ 3 f x ![i,j,k]
abbrev J4 (f : F → U) (x i j k l : F) := iteratedFDeriv ℝ 4 f x ![i,j,k,l]

-- Vector specialization lemmas, germwise.







lemma up₂ {S : F → U} {p : F} (h : ContDiffAt ℝ ω S p) (i j : F) :
    D i (fun z => D j S z) p = J2 S p i j := by
  change _ = iteratedFDeriv ℝ (1+1) S p (Fin.cons i ![j])
  rw [Analysis.cons_jet (h.of_le le_top)]
  simp only [D, iteratedFDeriv_one_apply, cons_val_zero]








section station
variable {S : (E × F) → ℝ} {ρ : E → F} {p : E}

def lift (ρ : E → F) (x : E) : E × F := (x,ρ x)



/-- For all real stationary germs here. This expresses just one tag, cut
later at critical claim on the actual Answer. No invertibility needed till
computing the vertical vector. -/
structure Parked (S : (E × F) → ℝ) (ρ : E → F) (p : E) : Prop where
  park : ContDiffAt ℝ ω S (lift ρ p)
  moving : ContDiffAt ℝ ω ρ p
  free : ∀ᶠ x : E in 𝓝 p,fderiv ℝ (fun y => S (x,y)) (ρ x)=0

namespace Parked
variable (h : Parked S ρ p)
include h




















end Parked
end station
end YM.AnalyticNext.CalendarScene.Jets
