import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Tablets
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.TiltAccount
import YM.Push.RELAY_DIFFERENCE.Applications
import YM.Push.SECTOR_MEASURE.Presented


/-!
# Gauge and mask columns unbundled: exponent convention

Push has one normalization **per bond**, one term per k, and the chosen masks
from the exact profile. Obtain preliminary graph identities with actual atoms still unsummed.
No compact support or differentiating R assumed. Don't strip any positivity before the integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Aff Aff.Mint  
open Centered Centered.Till  Footprint    Mixed Presented 
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x W : ℝ}

-- normalization becomes expectation over same k
lemma actual_tag (S : StepData c f) (k : S.Choices) (U : Config G f) : S.likelihood U k =
    (Fintype.card S.Choices:ℝ)⁻¹*((∏ i, αSite U i k)*∏ j,αBond U j k) := by
  have he : (Fintype.card S.Choices:ℝ)=(Fintype.card S.patch.FrameTag:ℝ)^Fintype.card (Site c)*
    (Fintype.card S.patch.Points:ℝ)^Fintype.card (Bond c) := by
      simp only [StepData.Choices,StepData.SitesChoice,
        Fintype.card_prod,Nat.cast_mul]
      congr 1 <;> simp [StepData.BondChoice]
  have hi : 0 < (Fintype.card S.Choices:ℝ) := by positivity
  unfold StepData.likelihood; simp only [αSite,αBond,prod_mul_distrib,prod_const,card_univ]
  calc
    _ = (Fintype.card S.Choices : ℝ)⁻¹ * (Fintype.card S.Choices : ℝ) * _ := by rw [inv_mul_cancel₀ hi.ne',one_mul]
    _ = _ := by rw [he]; ring_nf

open Next.Fluctuations.Sector









-- numeric exponent after removing cut from old family
lemma reacts (R : Rep G f) (x : ℝ) (U : Config G f) : R.beta*cutR R (till x) U + R.exponent U =
    R.v * Fintype.card (Site f) - averaged (fun s => reduced R (till x) (pull s 0 U)) - R.activities.additive R.p U := by
  -- proof like expel but don't cancel potential zero gas
  let n := till x; let a s := ∑ i, crown R.path R.clip n 1 R.p.threshold (pull s 0 U) i
  have he : R.path.inChannels R.clip R.p R.beta U =
      averaged (fun s => reduced R n (pull s 0 U)) + R.beta*cutR R n U := by
    have hk (s : Signed) : R.path.principal R.clip R.p R.beta (pull s 0 U) = reduced R n (pull s 0 U)+ R.beta * a s := by
      simp only [PathData.principal,a,reduced,cuff,Finset.sum_sub_distrib,mul_sub,mul_add]; abel
    have hv : R.path.inChannels R.clip R.p R.beta U = averaged fun s => reduced R n (pull s 0 U) + R.beta*a s := by
      simp only [PathData.inChannels,hk,averaged]
    rw [hv,av_add]; unfold a cutR averaged; rw [← Finset.mul_sum]; ring_nf
  unfold Rep.exponent; unfold n at he; rw [he]; abel



def apart (R : Rep G f) (U : Config G f) (x : ℝ) := -averaged (fun s => reduced R (till x) (pull s 0 U)) - R.activities.additive R.p U



-- atom prior to extraction, preserved




end YM.AnalyticNext.ConnectedActivity.Cab
