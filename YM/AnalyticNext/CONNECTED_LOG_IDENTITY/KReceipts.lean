import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction
import YM.Org.Theatre
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-!
# K receipts for the liberation-and-merge construction

Support only allows the one external flag-read exception AT V; pay
`inspected` if using these addresses also inside the next integration.
Keep any previous required eligibility. Terms may be used even if extras
not separately charged (then keep them as dependencies of the payload),
or via `sellsK` also putting the tests in the data, requiring earlier
nonzero activities themselves satisfy the tests.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Emit
open Lattice RG Wilson Pressure Filter Function Finset MeasureTheory
open AbsoluteSums Ursell Multiple Restore Attach 
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {n : Side} {G : Gauge} {ι κ : Type*} (X : ι → Support n) (Y I : κ → Support n)
    (hX : ∀ i,(X i).Nonempty) (hI : ∀ i,(I i).Nonempty) (hQ : ∀ i,I i ⊆ Y i)
    (p : BudgetPoint)
    (u : Config G n → ι → ℝ) (d : Config G n → κ → ℝ) (v : Clusters ι → ℝ) (test : κ → Config G n → Prop)

section Raw

structure Original : Prop where
  measF i : Measurable (fun V => u V i)
  measK i : Measurable (fun V => d V i)
  tests i : MeasurableSet {U | test i U}
  readsF i : LocalOn (X i) (fun V => u V i)
  readsK i : UsesFinal p.threshold (Y i) (fun V => d V i)
  asks i : UsesFinal p.threshold (Y i) (test i)
  affirms i V : d V i≠0 → test i V
  gaugeF i : GaugeInvariant (fun V => u V i)
  gaugeK i : GaugeInvariant (fun V => d V i)
  invariant i : GaugeInvariant (fun V => if test i V then (1:ℝ) else 0)
  -- can also state test_invariant explicitly



lemma raw_local (h : ∀ i, LocalOn (X i) (fun V => u V i)) (i : Clusters ι) :
    LocalOn (Restore.Z X i) (fun V => Restore.raw X (u V) i) := by
  intro U V he; unfold Restore.raw Gas.term; dsimp only; rw [prod_congr rfl (f:=fun j => u U (i.2 j)) (g:=fun j => u V (i.2 j))]
  exact fun j _ => h _ U V (agrees_mono he (Restore.Zcontains X i j))

lemma raw_meas (h : ∀ i, Measurable (fun V => u V i)) (i : Clusters ι) :
    Measurable (fun V => Restore.raw X (u V) i) :=
  (measurable_const.mul (Finset.measurable_fun_prod _ (fun j _ => h (i.2 j)))).div_const _

lemma raw_sym (h : ∀ i, GaugeInvariant (fun V => u V i)) (i : Clusters ι) :
    GaugeInvariant (fun V => Restore.raw X (u V) i) := by
  intro t V; unfold Restore.raw Gas.term; dsimp only; rw [prod_congr rfl (f:=fun j => u (Lattice.gauge t V) (i.2 j)) (g:=fun j => u V (i.2 j))];
  exact fun j _ => h _ t _











 -- κ may uncountable but finset bu












end Raw

variable [Countable κ] [Countable ι]



include hX

end YM.Push.LogIdentity.Emit
