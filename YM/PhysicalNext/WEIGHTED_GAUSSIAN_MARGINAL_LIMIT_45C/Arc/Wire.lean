import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Residue
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.TellerFold
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Primitives.CONNECTED_GAUSSIAN_CUMULANTS.Probe
import YM.Push.FREE_RESOLVENT.BlockRate

/-!
# Wires on which the two-log calculation holds

Uses only those SAME locally admissible reads, same chill/address
labels, not discarding trees after coordinate transfer. Identifies also
the exact linear answer (full A₀ T/psi dictionary here, no recut). No
cost to restore paths attempted. Need every pin (and every buffer due to
use of `Local` there) to fit already. Coordinates after selected gauge,
hence WITH its color choices. Does not claim a coherent overall sector
handoff. Context is this one post-P data, beta.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
open AnalyticBridge.LocalGaussianLaws  
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree Wisps Bid
open  Current FreeResolvent  Lift  MeasureTheory 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {tier : ℕ} {G : Gauge} {n c f : Side} {S : StepData c f} {x : ℝ}

lemma free_flat (v : Dir G n) : flatten (dColor G n 1 v) = tensor G (d 1 n) *ᵥ flatten v := by
  funext ⟨i,a,j⟩; exact congr_fun (component_mul (d 1 n) (flatten v) j) (i,a) |>.symm

lemma phase_eq (T : Tube G S) (F : Forest S.ratio) {H B : Bed} (h : Towers.Diagonal S H B T.R)
    {a l : ℝ} (ht : Floor H T.high f a l) (v : Dir G c) :
    flatten (dColor G f 1 (Lift.low T F v)) =
      tensor G (psi S H B T.R) *ᵥ flatten (dColor G c 1 v) := by
  have hx := spins S F H B T.R h ht
  let A:= neuron S F T.R
  have he : flatten (Lift.low T F v) = tensor G A *ᵥ flatten v := by
    funext ⟨i,a,j⟩
    change parts G 1 (Lift.low T F v) j (i,a)=component (tensor G A *ᵥ flatten v) j (i,a)
    unfold Lift.low; rw [Work.F04.parts_stretch,component_mul]; rfl
  simp only [free_flat,he, Matrix.mulVec_mulVec,← tensor_mul,A,hx]

section line
variable (F : Forest S.ratio) (T : Tube G S) (A : Stores S) (o : Site c)















end line
end YM.PhysicalNext.WeightedGaussianMarginal45C.Arc
