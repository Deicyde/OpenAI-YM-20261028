import YM.UVExtension.Rafter.Flight
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
variable {G:Gauge}{E Y:Type}[NormedAddCommGroup E][NormedSpace ℂ E] [NormedAddCommGroup Y][NormedSpace ℂ Y] {S:Set ℂ} {f:ℂ→ E}{x u v r:ℝ}
open Complex
lemma sway {m:Motion}{z:ℂ} (L:E→SL[gazeH m] Y)(hf:DifferentiableAt ℂ f (gazeH m z)): DifferentiableAt ℂ (fun u:ℂ=> L (f (gazeH m u))) z:=by
    suffices H: HasDerivAt (fun u:ℂ=> L (f (gazeH m u))) (L (deriv f (gazeH m z))) z from H.differentiableAt
    have h : Tendsto (gazeH m) (𝓝[≠] z) (𝓝[≠] gazeH m z):=by
       unfold gazeH; split_ifs
       · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
         · exact (continuous_star.tendsto z).mono_left nhdsWithin_le_nhds
         filter_upwards [self_mem_nhdsWithin] with d hd
         exact fun he => hd (star_injective he)
       exact tendsto_id
    apply hasDerivAt_iff_tendsto_slope.mpr; refine (L.continuous.continuousAt.tendsto.comp (hf.hasDerivAt.tendsto_slope.comp h)).congr' (Eventually.of_forall fun d=>?_)
    change L (_root_.slope f (gazeH m z) (gazeH m d))=_; simp only [slope_def_module,map_smulₛₗ]; rw [map_sub L]; rw [← map_sub,← map_inv₀]; rw [show gazeH m (gazeH m ((d-z)⁻¹))=(d-z)⁻¹ from ?_]; unfold gazeH; split <;> simp

variable [CompleteSpace Y]
lemma deckCL (g:ℂ→ E→L[ℂ] Y)(hv:∀ i,DifferentiableOn ℂ (fun z=> g z i) (ball 0 r))(hx:0<r)(hu:0≤ u)(hm:∀ z∈ball 0 r,‖g z‖≤u):DifferentiableOn ℂ g (ball 0 r):=by
    let T:=Spire.desk r hx; let v i:= g (T.call i)
    have h(x:E):= bumps (ball 0 r) (fun z=> g z x) (hv x)
    obtain ⟨f,hf,hg,hP⟩:= Rafter.flick (E:=Y) T v (LinearMap.id: E→ₗ[ℂ] E) (show DenseRange id from denseRange_id) hu (fun i=> ⟨fun z=>g z i,h i,fun _=>rfl,fun z hz=> ((g z).le_opNorm i).trans (mul_le_mul_of_nonneg_right (hm z hz) (norm_nonneg _))⟩)
    have hp:∃ f, f=g:=⟨g,rfl⟩
    refine (show DifferentiableOn ℂ f _ from hf _ id isOpen_ball (Set.mapsTo_id _) differentiableOn_id).congr (fun z hz=> ContinuousLinearMap.ext fun i=> ?_)
    exact Rafter.pair T (fun z=>g z i) (fun z=> f z i) (h i) (fun _ _ w h k=> (ContinuousLinearMap.apply ℂ Y i).differentiable.comp_differentiableOn (hf _ _ w h k)) (fun a=> congr_arg (fun w:E→L[ℂ] Y=> w i) (hg a).symm) _ hz

variable {L:E→L[ℂ] E}{z:ℂ}[CompleteSpace E] -- does not need finite dim!
lemma keel (L:ℂ→(E→L[ℂ] E))(hs:IsOpen S)(h:DifferentiableOn ℂ L S)(hp:∀ z∈S, Bijective (L z))(f:ℂ→ E) (hv:DifferentiableOn ℂ f S): DifferentiableOn ℂ (fun z=> (Lacing.steers (L z)).symm (f z)) S:=by
    have he z(hz:z∈S): IsUnit (L z):= ContinuousLinearMap.isUnit_iff_bijective.mpr (hp z hz)
    let g z:=Ring.inverse (L z); have hf:DifferentiableOn ℂ g S:=fun z hz=> ((differentiableAt_inverse (he z hz)).comp_differentiableWithinAt z (h z hz)) -- actual args
    refine (hf.clm_apply hv).congr (fun z hz=>?_); apply (Lacing.steers (L z)).injective; rw [LinearEquiv.apply_symm_apply,Lacing.steers_eq (L z) (hp z hz)]; unfold g; rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ (he z hz)]; rfl
end YM.UVExtension.Gale
