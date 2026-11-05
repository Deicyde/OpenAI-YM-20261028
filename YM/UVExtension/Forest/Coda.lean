import YM.UVExtension.Wet.Reigns
import YM.UVExtension.Upland.Plinth
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{hG:G.Simple}{M:Metals G}{P:Rolls M.p}{A:Alloy M P}{Q:Roost.Factor A} (S:Uses Q hG) (v:Keys S) {C:ℕ→ℝ}{W:Bid.Worth}(R:Legato.Bandage Q C W)
    (d m N n:ℕ)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T'"=> (Orchard.Path S v).levels
local notation "π"=> localSection G d
local notation "O!"=> hol G
open Metric Wet Wren
variable {V:Org.Bolt A}(a:Upland.Arc Q S V)
variable (x:Rose S)(hv : Tendsto (fun i=>(v i n).val) atTop (𝓝 x.val))
local notation "Y"=> landsK S v
local notation "K'"=> A.B.a.budget m
include n x S hv v
lemma yearly {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E]{F':ℕ→ℂ→ E} (h:Camp.SummitUV (Upland.Arc.radius S) F'): Arrives (fun i=> F' i ((v i n).val:ℂ)):=by
    obtain ⟨F,hF,h⟩:=h; have hp : TendstoLocallyUniformlyOn F' F atTop (ball 0 (Upland.Arc.radius S)):=by simpa using h 0
    have ht:(x.val:ℂ)∈ Camp.Broad A.B.a:= x.2
    let b:= Upland.Arc.radius S; have hx:(x.val:ℂ)∈ Metric.ball (0:ℂ) b:= x.2
    refine ⟨_,hp.tendsto_comp (hF.continuousOn _ hx) hx ?_⟩; rw [nhdsWithin_eq_nhds.mpr (isOpen_ball.mem_nhds hx)]; exact (Complex.continuous_ofReal.tendsto _).comp hv
include a
variable {ι:Type}{w:Filter ι}(t:ι→ℕ)(ht:Tendsto t w atTop)(hz:∀ i,m ≤ t i)
lemma tiding (m:ℕ) : Arrives (fun i=> (S.realBeat (v i n).val i n m).beta) ∧ Arrives (fun i=> let V:=S.realBeat (v i n).val i n m; Tabernacle.tuning (A.B.a.budget m) (A.B.a.clock.allowance m) (A.B.a.clock.forcedAllowance m) (V.activities.E,V.activities.K)):=by
   obtain ⟨ha,h⟩:= Upland.Arc.uv a m n
   have hx i (hi:m≤ i):= Upland.Arc.real S m n i hi (v i n).val (v i n).property
   have hp := (yearly S v n x hv ha); have hV:= (yearly S v n x hv h)
   exact ⟨(hp.post Complex.continuous_re).copy ((eventually_ge_atTop m).mono fun i hi=> congr_arg Complex.re ((hx i hi).2.2.2.2.2.1)), hV.copy ((eventually_ge_atTop m).mono fun i hi=> (hx i hi).2.2.2.2.2.2)⟩
include ht hz
variable [w.NeBot]
lemma treble : let V(i:ι):= S.realBeat (v (t i) n).val (t i) n m
     Notes w K' (drawer G _).reg (fun i=> (V i).activities.E)∧ Steady.Transit w (fun i=>(V i).activities.K) :=by
    intro T; let F' i:= ( (T i).activities.E,(T i).activities.K)
    obtain ⟨y,hy⟩:= (tiding S v n a x hv m).2
    apply Verso.won (x:=F') K' _ _ (Dales.fundedP m A.B.a|>.1) (Dales.fundedP m A.B.a|>.2) _ ⟨_,hy.comp ht⟩
    intro i; have hh:= (Vintage.YM.RG.History.Selected.represents (Orchard.selected S v) (t i) n m (hz i)).good; exact ⟨_,_,hh.labels⟩ -- `Tabernacle.rake`.
lemma signs : Span.StableR w (fun i=>S.realBeat (v (t i) n).val (t i) n m):=by
   let F i:= S.realBeat (v (t i) n).val (t i) n m; have hh:= treble S v m n a x hv t ht hz
   have hx : Steady.Transit w (fun n j V=> (F n).activities.regularOccurrence (F n).p j V):= TransitM.under (G:=G) hh.1
   obtain ⟨a,hb⟩:= (tiding S v n a x hv m).1; obtain ⟨T,Hr,h'⟩:=hx.rain; obtain ⟨C,hV,hY⟩:=hh.2.rain
   refine ⟨⟨fun _ _=>rfl,fun _ _=>⟨rfl,rfl⟩⟩,⟨a,hb.comp ht⟩,⟨C,hV,hY⟩,⟨T,Hr,h'⟩, fun j ε hε=>?_⟩
   filter_upwards [(hh.2.meters j).uv ε hε,(hx.meters j).uv ε hε] with w hV hz V; exact ⟨hV V,hz V⟩
end YM.UVExtension.Mast
