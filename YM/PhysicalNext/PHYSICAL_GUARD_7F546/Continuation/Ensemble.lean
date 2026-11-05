import Mathlib.RingTheory.Nilpotent.Exp
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Hop
import YM.Next.RANK.Ratios
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe
import YM.Push.PRICE_COMPILER.Post

/-!
# One application to ungauged moments with restored masks

Measurable in *this* Y, only at the stipulated d. Keep Γ and masks. Don't
claim product form for separation. Include a finite-average consumer (not
an average against *field-dependent* tag likelihoods--those not part of
these marginal laws). This deliberately uses uncut forecast and no claims
about computational footprints of that forecast. Leaves marked or kernel
reconstructions outstanding.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.PhysicalGuard7f546.Curved
open Filter Function Lattice RG Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Rows Tree Bid Gaussian Push.SectorMeasure Presented
open YM.AnalyticBridge.LocalGaussianLaws Current Lift Remote Local Assembly  
open MeasureTheory 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

open FreeResolvent (treeInverse insertion ix flatten tensor)
variable {G : Gauge} {c f n : Side} {S : StepData c f} {A : Stores S}
    {F : Forest S.ratio} {x : ℝ} {T : Tube G S}

-- Spend the genuine d parameter bounds needed for continuity in Y.
lemma portrait_sharp {Pt : Teller G} (hh : Pt.Funds S T) (F : Forest S.ratio)
    (A : Stores S) (x : ℝ) (V : Config G c) (k : S.Choices) (χ : Chi) (s : Geometry)
    (d : ℝ) (hd : 0<d) (hc : 2*d<firstRadius G) :
    Continuous (portrait T A F k x V s χ d) := by
  obtain ⟨a,b,ha,-⟩ := hh.feeds
  have hv := source_continuous T x V k (shots S x) A F χ d ha hd hc
  unfold portrait offCenter blame mulVec dotProduct
  apply continuous_pi; intro i
  have he j := (continuous_apply j).comp hv
  fun_prop

section profile
variable {Γ : Vec (In x A F (G:=G)) → ℝ}
variable {H L : Bed} {o : Site c} {l d D : ℕ} {V : Config G c} {z w} {ε Y U β : ℝ}
    {I E : Type} [Fintype I] [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]



-- average over a *finite* list of full k/F, without substituting a
-- conditional kernel probability in the tag slot. Same U arguments across
-- P's probes. Instance with profile `veil`: nonzero only on read guard,
-- not the broad-link profile as part of intact sector. Works whether or not
-- F is sold/generator history-produced. Taking R=actual polynomial allowed.

end profile
end YM.PhysicalNext.PhysicalGuard7f546.Curved
