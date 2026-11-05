import YM.FullVolume.Mark.Latch
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Das
import YM.Further.DENSE_MIXED_KERNELS.Hall
import YM.Further.DENSE_MIXED_KERNELS.Stroke
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.MergeProof.Orchestra
import YM.PhysicalNext.ORDERED_AFFINE_2B.Till
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sward.Hood
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "y"=> H.levels.clock.forcedAllowance i
variable {B H N p i Y}{X:ℕ→Support (H.S.side i p)}{M: Local.Raw F (H.S.side i p)}{f:Config G (H.S.side (i+1) p)→ℂ}{lead:F.Coeff}{w t r:ℝ}
lemma growing (S: Berths (Rout).p (Rout).activities (fun q=>joint B 0 (X q)))(h:Fancy B H N p i Y f X M lead w t r) (hx:H.Conv N p i)(he:Readable Y B (Rout).p WorkSite w): let P:=mint S M Y;
    Gig B H N p i Y f P lead t r ∧ Attainment (Rout).p 0 (coda B Y 0 X M Rout) r ∧
      profile (Rout).activities P.forced= profile (Rout).activities M.forced + hook (Rout).activities (Rout).p.threshold (coda B Y 0 X M Rout):=by
   intro Z'; obtain ⟨a,b,c,⟨h₁,h₂⟩,hp',hv,⟨pQ,q,hq,h₃⟩,hA,hC⟩:=h; let Z:= mint S M Y
   have hh:= (vigor hq h₁ he)
   rw [h₃] at hh
   have hκ:0<kappa H i:= Real.sqrt_pos.mpr (forcedPos ..)
   have hp:Tab Z 0 Rout (kappa H i) a (b+c):=tab_mint S h₁ hx.good hκ he hv
   have htX:1≤ turnCost (Rout).p.order (Rout).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   refine ⟨⟨usage S h₁ hx.good he,(value_mint S h₁ hx.good hκ he hv).trans h₂,?_,_,_,hp,hA⟩,stackFee hh ((le_mul_of_one_le_left hp.first htX).trans ((le_add_of_nonneg_right hp.second).trans hA)),budgetProfile S hv h₁ he hx.good hκ⟩
   obtain ⟨f,e,h1,h2,h3⟩ | hP := hC
   · exact le_trans (mul_le_mul_of_nonneg_left (sensor S h₁ he hv h1 h2) (zero_le_one.trans (orbitCost_one_le F))) h3
   exact le_trans (mul_le_mul_of_nonneg_left (size_mint S h₁ he hv lead) (zero_le_one.trans (orbitCost_one_le F))) hP
end YM.MergeProof
