import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Alabaster
import YM.PhysicalNext.PHYSICAL_JOINT_ENDPOINT_LOAD_F16.DLog.Script
import YM.Push.ABSOLUTE_SUMS.Coef
import YM.Push.SECTOR_MEASURE.Overlap

/-!
# The *actual* whole-color letters to put into Fsct

Here choose to keep long first-family pairs already as differences,
with the SAME k/Forest in the flat comparator, before Mayer. No burden
on a fresh orientation or read-forest. Actual compatible Slices (with
other normalization branches) still from the sector consumer's dictionary. Never applying these sums to an absolute load from distinct tag choices. Canonical transcripts here
BEFORE replacements of local diagonal paired letters in short-parent profiles. These aren't analytic extension grants. Keeps actual values at ANY B at our
letter tests (frozen reference at 1), good V, all addresses not erased.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.EndpointLoadF16.DetLong
open Function Filter Set MeasureTheory Lattice RG Wilson Pressure Tree Matrix
open Push.SectorMeasure Next.SectorChange Next.Fluctuations.Sector FreeResolvent FreeResolvent.TestD SelectedOrderedKernels
open AnalyticBridge AnalyticBridge.LocalGaussian AnalyticBridge.RelativeLogdet Physical Differential Fund WardBin.Lies
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {V : Config G c} {B : Directions G c}
    {n l k j : ℕ} {x a : ℝ} {T : Tube G S} {A : Stores S} {F : Forest S.ratio} {s : S.Choices} {q : Fund}
    {bp : BudgetPoint} {o : Site c}

abbrev GFirst (f : Side) := Bond f ⊕ Letter (Bond f) 1
abbrev Long (f : Side) := Letter (Bond f) 1 ⊕ Letter (Bond f) 0

def bolus (g : Key G f → Config G c→ℝ) (i : Bond f) := ∑ j : G.ColorIndex, g (i,j)
def chap (g : Letter (Key G f) j → Config G c→ℝ) (z : Letter (Bond f) j) :=
    ∑ i : Paint.paints G.ColorIndex z, g (Paint.hue z i)

lemma bolus_read (g : Key G f → Config G c→ ℝ) (i : Bond f) (V : Config G c) :
    bolus g i V=Paint.batch (fun i=>g i V) i := by rw [bolus,Finset.sum_apply]; rfl


section parts
variable (x T A F s)
def chapters : GFirst f → Config G c → ℝ := Sum.elim (bolus (simple x T A F s)) (chap (correction x T A F s))

def contrast (i : GFirst f) : Config G c → ℝ := chapters x T A F s i - (fun _ : Config G c => chapters x T (voidStore S) F s i 1)

def supplement : Letter (Bond f) 0 → Config G c → ℝ := chap (intervalCharge x T A F s)

def pitch : Long f → Config G c → ℝ := Sum.elim
    (fun i V => -(1/2:ℝ) * contrast x T A F s (.inr i) V)
    (fun i V => (1/2:ℝ) * supplement x T A F s i V)

def prelude (i : Bond f) (V : Config G c) := -(1/2:ℝ) * contrast x T A F s (.inl i) V
end parts



namespace Fund.Recital
variable (h : Recital q n k l a x A T F s V B)
include h









variable (h0 : Recital q n k l a x (voidStore S) T F s 1 0)
include h0



end Fund.Recital
end YM.PhysicalNext.EndpointLoadF16.DetLong
