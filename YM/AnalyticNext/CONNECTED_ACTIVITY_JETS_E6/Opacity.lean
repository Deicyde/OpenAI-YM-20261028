import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan


/-!
# Mark perturbations of incoming E

Actual relative calculations; regular mask held (also at λ=0). Schedules
can query lower-scale budgets, no new Path/kernel/θ, K histories follow
unchanged and share every already chosen address.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Opacity
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Gas Ursell Trees    Next.Foundations
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Tree.Forest S.ratio}
variable {W α μ C a : ℝ} (R : Rep G f)
variable {Q : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {L : Side}

/-- Variation, **within this transition**, not erasing a pressure in
some trajectory and asserting its Move. -/
def alter (v : ℝ) (R : Rep G f) : Rep G f := { R with activities := { R.activities with E:= v • R.activities.E } }

@[simp] lemma undo : alter 1 R=R := by unfold alter; rw [one_smul]







def key (S : StepData c f) (i : ℕ) : Head S := .inr (.inr (.inl (.inl (.inl i))))





variable (X : Coat T F)





end YM.ConnectedActivityE6.Opacity
