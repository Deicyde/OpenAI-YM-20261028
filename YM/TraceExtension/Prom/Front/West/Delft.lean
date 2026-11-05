import YM.MergeProof.West.Delft
import YM.TraceExtension.Prom.Front.West.Cedar
import YM.TraceExtension.Prom.Front.West.Dart
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Laurel
import YM.TraceExtension.Prom.Front.West.Mallow
import YM.TraceExtension.Prom.Front.West.Residual
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
/-!
  Variant of YM.MergeProof.West.Delft for dynamic stops. Pulse extension.
-/
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
variable (H:C.Makes)(hk:∀ i,C.ref (d i)≤k) (Xg:CeremonySky ξ c P R Ψ)
include Xg
lemma attireSky (U:LaunchSky C k ξ s z)(V:survivors C N k p U.pane (P k))(hx:Caff (G:=G) ξ τ (k-middleSky AX ξ.band k) u (m+1)) (hp:PlesseySky ξ Y c P R u)(hQ:2 ≤ u)
    (he:FitSky AX ξ.band k Y)(ht:Spaced (scouts C k) (seatsSky C ξ.band Y c.allow p))
    (hT:∀ i,ξ.cash τ*moneys C (d i) k N p (v i)≤ Perch.bill (-8) τ)
    (hi:∀ i,coin ((F i).W (v i)) ≤ ξ.principal τ)
    (hV:StakeXSky m Y ξ.band c.allow v H hk c (Hat τ^z)): ChastSky P c Ψ Y X1 ξ u (IssuedXSky C ξ.band Y c.allow p v) := by
   have hL:= kits Y v F hi
   apply legionSky Xg hL hx hQ he hp
   apply staunchSky Y v F Xg hL hx hQ
   exact admitsXSky H c.allow U.pane V m ξ.goal ξ.taylor ξ.era.coast.Q hk Y v c U.grant _ ξ.band ht hT (fun i=> (F i).coupon _) hV
end YM.Next.Rank.Tapes.West
