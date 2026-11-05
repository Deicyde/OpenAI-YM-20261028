import YM.UVExtension.Gale.Ship
import YM.UVExtension.Rainfall.Price
import YM.UVExtension.Cloud.Forks
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Gale
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard Metric Lamppost Motion Work.G08
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{d:ℕ}{F:Frame G d}{A:Hol G}{n m:Side}{P Q:BudgetPoint}
local notation "L'"=> RoutesF F n m P Q A
local notation "E₁"=> Cow G m P d A
local notation "E₀"=> Cow G n Q d A
local notation "N!"=> Bucket F Q A n
variable (S:Set ℂ)(L:ℂ→RoutesF F n m P Q A)
set_option synthInstance.maxHeartbeats 90000
structure Rains : Prop where
   vane (i:Option F.Index):DifferentiableOn ℂ (fun z=> (L z).vane i) S
   glass i v: DifferentiableOn ℂ (fun z=>(L z).glass i v) S
   peals i v:DifferentiableOn ℂ (fun z=> (L z).wing i v) S
   key i j: (L i).route=(L j).route

variable {S L} {r t:ℝ}
local notation "Z"=>ball (0:ℂ) r
variable (hr:0<r)(h:Rains (ball 0 r) L)(hc:∀ z∈Metric.ball 0 r, Counts (L z) t)
include hr h hc
open InputColumn Complex Lamppost
private lemma swift (v:Cow G m P d A): DifferentiableOn ℂ (fun z=> (L z).Pillow v) Z:=by
    let F'(i:Listing) z:= RoutesF.shell (L z) v i
    have hF(i): DifferentiableOn ℂ (F' i) Z:=by
       unfold F' RoutesF.shell; refine (rooms n F A Q (aisleN (code _) i)).differentiable.comp_differentiableOn (show DifferentiableOn ℂ (fun z=>RoutesF.roof (L z) v i) (ball 0 r) from ?_)
       rcases i with _|i|i
       · exact differentiableOn_const _
       · intro z hz; exact h.glass (key m i) _ z hz
       -- need cast route equals base using hp.
       let q:= (L 0).route
       have he z: (L z).route=q:= h.key z 0
       change DifferentiableOn ℂ (fun z=> Function.extend (L z).route (fun j=> (L z).wing j (v.2 j)) (0:ℕ→Bucket F Q A n) i) _; simp_rw [he]
       by_cases hx:i∈range q
       · obtain ⟨j,rfl⟩:=hx; simp_rw [q.injective.extend_apply]; intro z hz; exact h.peals j _ z hz
       simp_rw [extend_apply' _ _ _ hx]; exact differentiableOn_const _
    have he(i:Listing) z(hz:z∈Z): ‖F' i z‖≤ t * asset (L 0) v i:=by
        refine ((hc z hz).column v i).trans_eq ?_; unfold asset; rw [h.key z 0]
    exact differentiableOn_tsum_of_summable_norm ((shelter (L 0) v|>.summable).mul_left t) hF Metric.isOpen_ball he

lemma raft (v:ℂ→ E₁)(hv:DifferentiableOn ℂ v (ball 0 r)) (i:Option F.Index): DifferentiableOn ℂ (fun z=> (L z).rain (v z) i) Z:=by
    let f(z:ℂ): E₁→L[ℂ] N! := if hz:z∈Z then Counts.caravan (hc z hz) else 0
    have hF z(hz:z∈Z) x:f z x=(L z).Pillow x:=by unfold f; rw [dif_pos hz]; rfl
    have hu:0 ≤2*t:= mul_nonneg zero_le_two (hc _ (mem_ball_self hr)).calm
    have hf:DifferentiableOn ℂ f Z:=by
       refine deckCL f (fun i=> (swift hr h hc i).congr (fun z hz=> hF z hz i)) hr hu (fun z hz=> ?_) -- module params
       exact (f z).opNorm_le_bound hu fun i=> by rw [hF z hz]; exact (hc _ hz|>.serves i).2
    let q:=rooms n F A Q (aisleN (code Listing) (.inl ()))
    have hh : DifferentiableOn ℂ (fun z=> q ((L z).vane i)) Z:= q.differentiable.comp_differentiableOn (h.vane _); exact (hh.add (hf.clm_apply hv)).congr (fun z hz=> by change _ = q _+ f z (v z); rw [(hc z hz).rains,hF]; exact hz)
end YM.UVExtension.Gale
