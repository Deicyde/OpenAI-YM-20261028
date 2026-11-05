import YM.MergeProof.Bouquet
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Reseve

set_option autoImplicit false
noncomputable section
namespace YM.Merge.Joins
open Function Set Filter Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory
open Progress.DirectedRecipe PhysicalNext.Repeat Mallow
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{c:Side}(P:BudgetPoint){A ι:Type}{x:A}{t:ι→ℝ}{v:ι→A}{F:A→ℝ→ Code G c}(X:Pipes G c)(W: ℕ≃ Pellet X)(d: Tap G c)
variable (h:∀ i V,Joins x t (fun a y=> F a y i V) v)
include h
lemma harvest (i : ℕ)(V:Config G c): Joins x t (fun a y=> solid W P (spice d (F a y)) i V) v:=by
   unfold solid; split
   · let f (i:Label)(a:A)(y:ℝ):= reach (spice d (F a y)) i V
     have hi i : Joins x t (f i) v:=by rcases i with j|j;exact h _ _;exact constant (Real.exp (d.logarithm j V)-1)
     have hz:= prod (W i).val f (fun i _=> hi i); convert hz using 1; ext; simp [f]
   exact constant _
lemma in_final (i:ℕ)(V:Config G c):Joins x t (fun a y=> final.frigid X d (F a) P y i V) v:= by
   change Joins x t (fun a y=> solid (folio G _) P (spice (Rack.widen X d) (stuff (Rack.upK X) (F a y))) i V) v; apply Joins.harvest; intro i V; by_cases hp:i∈ range (Rack.upK X)
   · obtain ⟨i,rfl⟩:=hp; simp_rw [stuffed]; exact h _ _
   simp_rw [blank _ _ hp]; exact constant _
end YM.Merge.Joins
