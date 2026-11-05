import YM.MergeProof.West.Cassia
import YM.TraceExtension.Prom.Front.West.Canvas
import YM.TraceExtension.Prom.Front.West.Fix
import YM.TraceExtension.Prom.Front.West.Mural
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

set_option quotPrecheck false
local notation "O"=> offerNowSky E (vista R W hk)
local notation "F"=> Array.reorient (Ship.yardSky C b c.allow p) T.1 (spunW R W hk.le (vantageSky E))

include hP hx t Hv he he' hr H hs hu hp
lemma f_inaleSky (M:ℝ) (hM : 1≤ M)(m:ℝ) (hD:gentility B ε r D n ≤ m) (hm:0≤m) (hz:∀ v:modes (Fin n),v.val⊆ T.2.val.val.val → ‖text (vantageSky E) (heads R W hk.le v)‖ + m ≤ M):
    let j:= T.2; let V:= gloryFtSky x b p c.allow hk.le h T.1 j.val (anneals C c i) (vista R W hk.le j.val.val); ‖(leadFtSky E (offerNowSky E (vista R W hk))).part j.val.val-V U‖ ≤ grater n M m:=by
   intro j V'; let L:=leadFtSky E (offerNowSky E (vista R W hk)); let O':=planterFtSky E (offerNowSky E (vista R W hk)); let K:=Ship.yardSky C b c.allow p
   let L':= Array.reorient K T.1 (t_cum R W hk.le (vantageSky E)); let W':= (F)
   have hh:= expanders R W hk.le (vantageSky E); have hp : Expands L' W':= by
     refine ⟨?_,?_⟩
     · dsimp only [L',Array.reorient]; split; · exact (congr_arg star hh.1).trans (star_zero _)
       exact hh.1
     rw [show Poly.pass L'= _ from (Array.turns_pass K T.1 _).symm,hh.2]
   have hX : V' U=L'.part j.val.val:= by unfold L' Array.reorient V' gloryFtSky Edition.dot; dsimp only [K]; split <;> rfl
   have ht:W'.part (quiet _)=1:=by rw [← hp.2]; exact Poly.pass_part _ hp.1
   rw [hX, hp.uniq (connected_spec W' ht)]; apply crumbling M m hM hm
   intro i hi; have hu:= (flight_paySky E W hP hx t Hv he he' hr H hs hu ‹∀ u : Manner n,_› i hi).trans hD
   have hs:=hz i hi; let D:= ‖text (vantageSky E) (heads R W hk.le i)‖; have hD : ‖W'.part i‖=D:= by dsimp only [W',Array.reorient];split; exact norm_star _; rfl
   refine ⟨?_,hD.trans_le (by linarith only [hs,hm]),hu⟩
   let u:=W'.part i;exact ((norm_sub_norm_le (O'.part i) u).trans hu)|> (fun hx=> by change ‖O'.part i‖≤M; unfold u at hx;rw [hD] at hx; unfold D at hx;linarith only [hx,hs])
end YM.Next.Rank.Tapes.West
