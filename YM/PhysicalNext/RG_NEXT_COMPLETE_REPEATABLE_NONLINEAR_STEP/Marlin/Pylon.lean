import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Trimmings
/-!
 # Peletting K without ANY Early E-Hessian constraint. BudgetPoint reweighted
 (`raiser`) giving the needed EXP+1 after merge; calibrator same threshold (including
 at the boundary). At the actual Latch output every new eligibility explicitly checked.
 Trial Valid used only for impersonal all-E-zero label physical comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Marlin
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Poll Pond MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Metric Progress.DirectedRecipe Payments Ovens Ovens.Pipes
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c L:Side} {B : BudgetPoint} {X : Pipes G c}
variable {d : Tap G c} {e w p h v : ℝ}
abbrev raiser (P : BudgetPoint): BudgetPoint := {P with supportExponent:=P.supportExponent+1, exponent_pos:=add_pos P.exponent_pos zero_lt_one }
def hak (X : Pipes G c) : ℕ ≃ X.Pellet := (X.encoding).some
def pluck (B:BudgetPoint) (X:Pipes G c) : Listing G c:= ⟨X.reg, addr (hak X) B⟩
def poursP (B : BudgetPoint) (X : Pipes G c) (d:Tap G c) : Collection.Source G c:= ⟨d.regular,solid (hak X) B d⟩
def dummy (d:Tap G c): Tap G c:= {d with regular:= fun _ _=>0}
lemma ledger {u: ℝ} (H : X.Digests (dummy d) (raiser B) 0 u) (s:Signed) (b:Site c) (M : (X.pours d).Moves s b): Nonempty (((pluck B X).read (poursP B X d)).Moves s b):= by
  obtain ⟨q⟩:= Work.H03.fused_moves (hak X) H s b; exact ⟨⟨M.ep,q.kp,M.reg_site,M.reg_support,q.forced_support,q.forced_inventory,q.forced_tests,M.valuesE,q.valuesK⟩⟩
lemma pulpy_T (H : Ingredients X (dummy d) (raiser B) 0 w) (V:Config G c): ((pluck B X).read (poursP B X d)).gas B V=(X.pours d).gas B V*Real.exp (∑' i,d.logarithm i V):= by
  obtain ⟨a,b,c,h,hf,hu⟩:=H.pays; exact (Work.H01.gathered h V (F:=hak X)).tsum_eq
lemma sous (H : Ingredients X (dummy d) (raiser B) 0 w) (V:Meadow.Budget B X.reg d.regular e) (hp:∀ s b,Nonempty ((X.pours d).Moves s b)) : Collection.Local (pluck B X) B (poursP B X d) e w:= by
  obtain ⟨f,h,hf⟩:=V
  obtain ⟨a,b,u,h',hB,hQ⟩:= H.pays
  obtain ⟨z,hZ,hr⟩:= Work.H02.answer G c X (dummy d) (hak X) _ _ a b _ (raiser B) hQ h' hB
  have he := Work.H03.fused_forcedFamily (hak X) h'
  refine ⟨(fun i=>(hf i).1), ?_, fun s b=> ledger h' s b (hp s b|>.some), ⟨_,fun i=> (hf i).2,h⟩, ⟨_,hZ,fun x=>?_⟩⟩
  · exact ⟨he.sym,he.symtest,he.meas,he.meas_test,he.reads,he.reads_test,he.permit⟩
  convert hr x using 2 with i; simp only [BudgetPoint.mass]; rw [mul_comm (z i)]; rfl

-- Verify fittings h'D projection
lemma cannon
    (hV : (X.pours d).ForcedFamily B) (hm : ∀ s b, Nonempty ((X.pours d).Moves s b))
    (ha : ∀ i, Trio.Tidy B (X.softer i) (d.logarithm i))
    (hd : ∀ i V,d.logarithm i V≠0→¬Healthy B.threshold (X.softer i) V)
    (hf : ∀ (s:Signed) (b:Site c), ∃ v : Equiv.Perm ℕ, (∀ i,X.softer (v i)=(X.softer i).image (Lattice.affine s b)) ∧ ∀ V i,d.logarithm (v i) V=d.logarithm i (pull s b V))
    {p q: ℕ→ℝ} {a b κ : ℝ} (hr : rooted d p q) (hp:hardCost (raiser B) X p a) (hq:softCost (raiser B) X q b) (hR: Payments.Rates B.B w a b κ) : Ingredients X (dummy d) (raiser B) 0 w:= by
  refine Payments.tender ?_ ?_ hp hq (show rooted (dummy d) p q from hr) hR
  · refine ⟨⟨fun i=> by exact CouplingShape.reg_const _,fun _=>rfl, fun i _ a b _ _ =>?_⟩,?_,?_,hd,fun i=>(ha i).invariant,fun i=>(ha i).uses,fun i=>(ha i).borel,hf⟩
    · unfold logHessian; change iteratedFDeriv ℝ 2 (fun _: Directions G c=> (0:ℝ)) 0 _=0; simp
    · exact ⟨hV.sym,hV.symtest,hV.meas,hV.meas_test,hV.reads,hV.reads_test,hV.permit⟩
    intro s b; obtain ⟨q⟩:= hm s b; exact ⟨⟨q.ep,q.kp,q.reg_site,q.reg_support,q.forced_support,q.forced_inventory,q.forced_tests,fun i v=> rfl,q.valuesK⟩⟩
  refine ⟨fun i=>0,fun i=>?_,fun i=> by simp [SumBudget,BudgetPoint.mass]⟩; exact CouplingShape.sup_larger (CouplingShape.sup_const 0) (le_of_eq abs_zero)
end YM.PhysicalNext.Repeat.Marlin
