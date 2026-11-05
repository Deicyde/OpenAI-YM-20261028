import YM.MergeProof.Rosin
import YM.MergeProof.Elder
import YM.TraceExtension.Quince.Guild
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Nick
open Finset Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open YM.PhysicalNext.Repeat.Quince Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}(B:SectionData F) (H : History G) (N p i : ℕ) (Y : Hol G)
local notation "Rout" => H.rep N p i
local notation "Old" => H.rep N p (i+1)
local notation "WorkSite" => H.S.side i p
local notation "StartSite" => H.S.side (i+1) p
local notation "g₀" => Config G StartSite → ℂ
local notation "y"=> H.levels.clock.forcedAllowance i
open Source
-- already before jet uniqueness
lemma atom_lead {X:ℕ→Support WorkSite}{M: Push.Local.Raw F WorkSite}{v:F.Coeff}{f:g₀}{t u r k :ℝ}(h:Fancy B H N p i Y f X M v t u r)(hh:H.Conv N p i)(he:Push.Local.Readable Y B (Rout).p WorkSite t)(hq:orbitCost F* F.coeffSize ((M.seed+∑' j,M.row 0 X Y (Rout).p.threshold j)-v)≤ k) : PaidAtom B H N p i Y f v k r:=by
    obtain ⟨a,b,c,⟨h₁,h₂⟩,⟨S⟩,hv,hZ,hA,-⟩:= h; let Z:=Guard.mint S M Y
    have hκ:0<kappa H i:=Real.sqrt_pos.mpr (forcedPos ..)
    refine paid_center (fun s=> hh.good.labels.moves s 0) he.sound (usage S h₁ hh.good he) ((value_mint S h₁ hh.good hκ he hv).trans h₂) (tab_mint S h₁ hh.good hκ he hv) hq hA
end YM.MergeProof.Nick
