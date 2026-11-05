import YM.MergeProof.West.Lais
import YM.MergeProof.West.Laurel
import YM.MergeProof.West.Residual
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Bonfire



/-!
# Main budget to boundary l at ANY spec eligibility

Same winding as primary stamp. still needs N numerics/vantage. Eligibility by actual Launch from callers. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter Paint Vac.Numbers
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge} {C:Family G}{N n p k m u:ℕ}{ξ:Purse}{R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s z:ℝ}{Ψ:AtlasData G C.S p}
variable {d : Fin (m+1)→ℕ} (Y:Points (m+1))(v:(i:Fin (m+1))→ C.label (d i))
    (F:(i:Fin (m+1))→ StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q Ψ)
set_option quotPrecheck false
local notation "AX" => C.path.levels
local notation "τ"=>clim AX k
local notation "X1" => (fun i=> prefaced (F i) (v i) (Station.choose C.path.levels ξ.band k Y i))
variable (H:C.Makes)(hk:∀ i,C.ref (d i)≤k) (Xg:Ceremony ξ c P R Ψ)
include Xg
lemma attire (U:Launch C k ξ s z)(V:survivors C N k p U.pane (P k))(hx:Caff (G:=G) ξ τ (k-middle AX ξ.band k) u (m+1)) (hp:Plessey ξ Y c P R u)(hQ:2 ≤ u)
    (he:Fit AX ξ.band k Y)(ht:Spaced (scouts C k) (seats C ξ.band Y c.allow p))
    (hT:∀ i,ξ.cash τ*moneys C (d i) k N p (v i)≤ Perch.bill (-8) τ)
    (hi:∀ i,coin ((F i).W (v i)) ≤ ξ.principal τ)
    (hV:StakeX m Y ξ.band c.allow v H hk c (Hat τ^z)): Chast P c Ψ Y X1 ξ u (IssuedX C ξ.band Y c.allow p v) := by
   have hL:= kits Y v F hi
   apply legion Xg hL hx hQ he hp
   apply staunch Y v F Xg hL hx hQ
   exact admitsX H c.allow U.pane V m ξ.goal ξ.taylor ξ.era.coast.Q hk Y v c U.grant _ ξ.band ht hT (fun i=> (F i).coupon _) hV
end YM.Next.Rank.Tapes.West
