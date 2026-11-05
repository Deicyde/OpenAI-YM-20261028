import YM.MergeProof.West.Liza
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open MeasureTheory Cells Edition Filter
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G:Gauge}{N n p k q i l j d D m u:ℕ} {C:Family G}{x:Points m} {ξ:Purse} {R:Lead G C.S p} {c:Course C N p k}{P:(i:ℕ)→ Rep G (C.side i p)}{s:ℝ}{Ψ:AtlasData G C.S p}
section
open MergeProof.Accent
variable (V:Fin m→ poly (Chamber G C.S k p))

end
section
variable (x : Points m)(j:Fin m)

end
section
variable {d : Fin n → ℕ} (x:Points n)(v:(i:Fin n)→ C.label (d i))
   (F:(i:Fin n)→ StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q Ψ)

local notation "B" => ξ.band
local notation "AX" => C.path.levels
local notation "T" => Ship.yardSky C ξ.band c.allow p
local notation "Y" => (fun i => prefaced (F i) (v i) (Station.choose AX B k x i))

set_option quotPrecheck false

variable (Xg:CeremonySky ξ c P R Ψ) (hv:Kith (A:=C.path.levels) Y x ξ)
    (hq:Caff (G:=G) ξ (clim C.path.levels k) (k-middleSky C.path.levels ξ.band k) u n)
include Xg
lemma x_journeySky (v' : (Ship.yardSky C ξ.band c.allow p).Cell) (j:Fin n)(g:ℝ)(U):
   let t:=solitaire x j ξ p k C.path.levels
   gloryFtSky (C:=C) x ξ.band p c.allow le_rfl (beforeSky AX B k) v' t.val g (vista R Y le_rfl t.val.val) U=
       dot ((T).hand v') (signet 0 g ((F j).W (v j)) (pull ((T).omega v') (seatsSky C B x c.allow p (v',j)) U)):=by
   intro t; have ht:= journeySky x (fun _=> v j) (F j) Xg.sens c.allow j v' g U
   simp only [gloryFtSky]; rw [x_head x j (C:=C), show t.val.val= Glyph.slot j from rfl,x_cept (C:=C) (R:=R) Y j]
   simpa only [jacketPol,glorySky, polygon,oneRoot,center_shelf] using! ht
end
