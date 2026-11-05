import YM.MergeProof.West.Fix
import YM.TraceExtension.Prom.Front.West.Canvas
import YM.TraceExtension.Prom.Front.West.Karin
import YM.TraceExtension.Prom.Front.West.Mural
import YM.TraceExtension.Prom.Front.West.Rose
import YM.TraceExtension.Prom.Front.West.View
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Camps
import YM.TraceExtension.Prom.Hill.Joints
import YM.TraceExtension.Prom.Hill.Station
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes.West
open Function Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Relation Finset Marker
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
open MeasureTheory Cells Edition
variable {G:Gauge}{N n p k q i d D:ℕ} {C:Family G} {R:Lead G C.S p}
   {b:ℝ} {c:Course C N p k}{x:Points n}{hk:i<k}{h:middleSky C.path.levels b k ≤ i}
   {T τ U ε g B Y L} (E:StageNowSky (d:=d) c R x b hk h q T τ U ε)

variable (W: Fin n → poly (Chamber G C.S k p))
variable (hP : ∀ u,vista R W hk u ≠ 0 → ∃ i : ViewFt C k b p d x hk,i.val.val=u)
variable (hx:roomTestSky C.path.levels b k p d q) (t:Metal b c R hk ε τ g B Y L) (Hv:Healthy g (d_olmSky x b q (walls (clim C.path.levels i)) c.allow hk.le T.1 T.2.val) U) (he: 0 < ε) (he':ε≤1)
   {r:ℝ} (hr:0≤r)
variable (H:∀ u, Poetic (vista R W hk u)) (hs:∀ u,totalDegree (vista R W hk u)≤ D) (hu:∀ u,coin (vista R W hk u)≤ r) (hp:∀ u : Manner n,∀ i'∈(vista R W hk u.val).vars,spotFt b (i+1) d (show i+1≤k from hk) x u i' (C:=C))

variable {W}
def vantageSky (_ : StageNowSky (d:=d) c R x b hk h q T τ U ε) := let D:=basisFtSky c x b i c.allow hk.le h T.1 T.2.val U; rigid D
variable (W)
set_option quotPrecheck false
local notation "F"=> Array.reorient (Ship.yardSky C b c.allow p) T.1 (spunW R W hk.le (vantageSky E))
include hP hx t Hv he he' hr H hs hu hp
lemma flight_paySky (v:modes (Fin n)) (hv:v.val ⊆ T.2.val.val.val) : ‖(planterFtSky E (offerNowSky E (vista R W hk))).part v-(F).part v‖ ≤ gentility B ε r D n:=by
  let Y:=sprout (Fin n) (primeLog _) v
  have hx (j : Fin E.count) (z) : (Poly.pass (p_lanterSky E (offerNowSky E (vista R W hk)) j z)).part v=traySky E Y (vista R W hk) j z:= by
     let V:=p_lanterSky E (offerNowSky E (vista R W hk)) j z; change (Poly.pass V).part v= (medicine (sprout _ (primeLog _)) V).part v; rw [diaper,infancy]
  have ht:(planterFtSky E (offerNowSky E (vista R W hk))).part v=plaidFtSky E (traySky E Y (vista R W hk)):=congr_arg (plaidFtSky E) (funext fun i=>funext fun j=> hx i j)
  rw [ht]
  let Z := vantageSky E
  have hf : (F).part v= dot ((Ship.yardSky C b c.allow p).hand T.1) (text Z (heads R W hk.le v)):= by dsimp only [Array.reorient,Edition.dot];split_ifs <;> rfl
  rw [show (F).part v=platterSky (T:=T) (R:=R) (c:=c) (hk:=hk) (h:=h) (U:=U) Y (vista R W hk) by rw [hf,platterSky,resists,show heads R W hk.le v=_ from shelving R hk _]; rfl]
  apply (sweepSky E Y (vista R W hk) hP ‹roomTestSky _ _ _ _ _ _› t Hv he he' hr H hs hu hp (fun w h j hj=> (embraces.prime.knees v w h j hj).trans hv)).2.trans
  exact Finset.single_le_sum (fun u _=> grantS_nn (sprout (Fin n) (primeLog _) u) _ _ _ D t.grain he.le hr) (Finset.mem_univ v)

end YM.Next.Rank.Tapes.West
