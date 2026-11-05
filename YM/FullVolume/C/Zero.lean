import YM.FullVolume.C.Brawn
/-! Each layout space contains zero. Keep predicate & symmetry discipline. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Rain
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {n : Side} (R : Rep G n)
def initialBed (i:ℝ) : Rep G n:= {R with activities:= ⟨R.activities.reg,R.activities.forced,0,0⟩, beta:=i, v:=0}
lemma initialBed_valid {u v} (h:R.activities.Valid R.p u v) (i:ℝ) : (initialBed R i).activities.Valid R.p u v:=by
  let A := (initialBed R i).activities; change A.Valid ..
  obtain ⟨hr,hf,hm,hw,hh⟩:=h
  refine ⟨⟨fun x=> CouplingShape.reg_const _,fun _=> rfl, fun j hj x y _ _=>?_⟩,?_,?_,?_,?_⟩
  · change logHessian (fun _=> 0) x y=0; simp [logHessian]
  · exact ⟨fun _ _ _=>rfl, hf.symtest, fun _=>measurable_const,hf.meas_test, fun _ _ _ _ _=>rfl,hf.reads_test,fun _ _ h=> (h rfl).elim⟩
  · intro s b; obtain ⟨p⟩:= hm s b; exact ⟨p.ep,p.kp,p.reg_site,p.reg_support,p.forced_support,p.forced_inventory,p.forced_tests,fun _ _=>rfl,fun _ _=>rfl⟩
  · obtain ⟨f,h',hk⟩:= hw; exact ⟨f,fun j=> CouplingShape.sup_larger (CouplingShape.sup_const _) ((le_of_eq abs_zero).trans (h' j|>.1)),hk⟩
  obtain ⟨f,h',hk⟩:= hh; refine ⟨f,fun j=>⟨(h' j).1,fun U=>(by change ‖(0:ℝ)‖ ≤_; rw [norm_zero]; exact h' j|>.1)⟩,hk⟩
lemma remains (p : BudgetPoint) (A : Activities G n) (t : ℝ) (ht:0≤t) : deviation p A A t:=by
  exact ⟨0,0,fun _=>⟨le_rfl,fun _ _ _ _ _=>by simp⟩,fun i=>⟨le_rfl,fun _=> by simp⟩,by simp [BudgetPoint.mass, SumBudget,ht],by simp [BudgetPoint.mass, SumBudget, ht]⟩
lemma initialBed_curve (s) : Curve R.p (initialBed R) s:=
  ⟨continuousOn_id,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,
    fun _ hu x _=>Eventually.of_forall (fun y=> remains R.p (initialBed R x).activities _ hu.le)⟩
lemma unchanged (s) : Curve R.p (fun (_:ℝ)=> R) s :=
  ⟨continuousOn_const,continuousOn_const,fun _ _ _ _=>rfl,fun _ _ _ _=>rfl,
    fun _ hu _ _=>Eventually.of_forall (fun _=>remains R.p R.activities _ hu.le)⟩
end YM.PhysicalNext.Repeat.Rain
