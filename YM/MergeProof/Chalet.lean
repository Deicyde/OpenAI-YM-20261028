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
def Fancy (f : g₀) (X : ℕ → Support WorkSite) (M : Raw F WorkSite) (lead : F.Coeff) (w t r : ℝ) := ∃ a b c : ℝ, Arrival B H N p i f X M ∧
      Nonempty (Berths (Rout).p (Rout).activities (fun q => joint B 0 (X q))) ∧
      Tare M 0 X Y B Rout w (H.levels.clock.forcedAllowance i) (kappa H i) a b c ∧
      (∃ u v:ℝ, Planned.GuardedAtom.Deck M 0 X Rout (kappa H i) u v ∧ factor Y B (Rout).p.supportExponent w *u=a) ∧
      turnCost (Rout).p.order (Rout).p.power*a+(b+c) ≤ r ∧
        ((∃ (g : ℕ → Directions G WorkSite → ℂ) (e : ℝ), Models Y 0 X (Rout).p M lead e g ∧ 0≤e ∧ orbitCost F*(errorPrice Y F*e) ≤ t) ∨
          orbitCost F*(F.coeffSize (M.seed-lead)+a) ≤ t)
-- traces consumed: stronger unturned cost orientation. From f into output & degrees, V' profile
structure Gig (f:g₀)(P:Coefficient F WorkSite)(lead:F.Coeff)(c v:ℝ) :Prop where
    format:P.Format 0 Y Rout
    agrees:P.density 0 B Rout= blast H N p i d f
    leadP:orbitCost F*F.coeffSize (P.x-lead)≤c
    future:∃ a b:ℝ, Tab P 0 Rout (kappa H i) a b ∧ turnCost (Rout).p.order (Rout).p.power*a+b ≤ v
variable {B H N p i Y}{X:ℕ→Support (H.S.side i p)}{M: Local.Raw F (H.S.side i p)}{f:Config G (H.S.side (i+1) p)→ℂ}{lead:F.Coeff}{w t r:ℝ}
lemma grow (h:Fancy B H N p i Y f X M lead w t r) (hx:H.Conv N p i)(he:Readable Y B (Rout).p WorkSite w): ∃ P:Coefficient F WorkSite,
    Gig B H N p i Y f P lead t r ∧ Attainment (Rout).p 0 (coda B Y 0 X M Rout) r ∧
      profile (Rout).activities P.forced= profile (Rout).activities M.forced + hook (Rout).activities (Rout).p.threshold (coda B Y 0 X M Rout):=by
   obtain ⟨a,b,c,⟨h₁,h₂⟩,⟨S⟩,hv,⟨pQ,q,hq,h₃⟩,hA,hC⟩:=h; let Z:= mint S M Y
   have hh:= (vigor hq h₁ he)
   rw [h₃] at hh
   have hκ:0<kappa H i:= Real.sqrt_pos.mpr (forcedPos ..)
   have hp:Tab Z 0 Rout (kappa H i) a (b+c):=tab_mint S h₁ hx.good hκ he hv
   have htX:1≤ turnCost (Rout).p.order (Rout).p.power:= one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
   refine ⟨Z,⟨usage S h₁ hx.good he,(value_mint S h₁ hx.good hκ he hv).trans h₂,?_,_,_,hp,hA⟩,stackFee hh ((le_mul_of_one_le_left hp.first htX).trans ((le_add_of_nonneg_right hp.second).trans hA)),budgetProfile S hv h₁ he hx.good hκ⟩
   obtain ⟨f,e,h1,h2,h3⟩ | hP := hC
   · exact le_trans (mul_le_mul_of_nonneg_left (sensor S h₁ he hv h1 h2) (zero_le_one.trans (orbitCost_one_le F))) h3
   exact le_trans (mul_le_mul_of_nonneg_left (size_mint S h₁ he hv lead) (zero_le_one.trans (orbitCost_one_le F))) hP
end YM.MergeProof
