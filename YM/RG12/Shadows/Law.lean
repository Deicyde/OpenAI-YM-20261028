import YM.RG12.Shadows.Launch
/-! Retain order per temperature on bona fide projections on Hot platform -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Sanction
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak
open WardBin.Lies Push.PriceCompiler Foramen Gate Planned.AtomRegular.Foliage
open YM.RG12.Shadows
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{V:Loom G}
namespace Barque
variable (B:Barque V)(M:Leaf B.A)
variable {T':Anthem V.n}{d A κ L t:ℝ}{u:Chi}{p:Prices G B.I}(H:B.Quay T' d κ A L t u)
include H
lemma unifies : (lamp6 B.X B.a B.X.V).PosDef :=by have hv:=(H.particular.self_of_nhds.1).submatrix (scoop B.X B.a).injective; change (lamp6 B.X B.a (B.tour 0)).PosDef at hv; rwa [B.j1] at hv
lemma stems : Meristem (B.twin M d u) 0 B.cloud9 V.n:=by
    obtain ⟨e,hE,hs⟩:= H.heat
    unfold cloud9 C6; rw [Function.comp_apply,B.j1]; apply (Mercury.corridor B.X B.chip B.A B.a B.q u B.b V.D B.H.laws.intake hE M H.cool (B.center.symm ▸ flowJourney 1 B.U) _ H.ranks H.caps (H.healthy.mono (fun x hx s h=> (hx s h).1))).1
lemma kernels {C:ℝ}(U:B.Horn M C):
   (fun x:Panels 2=> M.cinema (vary B.X (B.tour x)) {Opacity.key B.S B.chip} V.W V.o.a B.Q.table B.Q.halo (podium B.S G B.Y B.X.B)-
     B.a.hymn B.T B.fuel B.q B.b B.X.k U.g (magic V.D B.A.p B.A.beta u) 1 (B.tour x)) =ᶠ[𝓝 0] (fun x=> ∫ z,B.twin M d u x z ∂B.cloud9):=by
  obtain ⟨e,hE,hs⟩:= H.heat
  let S:=lamp6 B.X B.a B.X.V; have hC : B.cloud9=Gaussian.cloud S:= by unfold cloud9 C6; rw [Function.comp_apply,B.j1]
  filter_upwards [H.healthy,H.particular,hs, (Mercury.corridor B.X B.chip B.A B.a B.q u B.b V.D B.H.laws.intake hE M H.cool (B.center.symm ▸ flowJourney 1 B.U) B.cloud9 H.ranks H.caps (H.healthy.mono (fun x hx s h=> (hx s h).1))).2] with x he hi hs hz
  have hj:= B.unifies H
  have hh:= Mercury.pop6 B.X B.chip B.A B.a B.H.laws.intake B.curtains B.living.sails.room hE hs M U.turn H.cool H.stays B.Q.halo B.Q.table V.W hj hi.1
  have hp:= Mercury.pop9 B.X B.chip B.A B.a B.q u B.b V.D B.H.laws.intake B.curtains hE hs M U.g U.issue U.hs H.cool H.stays hj hi.2 he
  rw [hh,hp,← hC]; exact (integral_sub hz.1 hz.2).symm -- S prism hC matches?
lemma hush (z:Prices G B.I)(hz:B.tongs < ‖z‖): (fun x=>B.twin M d u x z) =ᶠ[𝓝 0] 0:=by
  obtain ⟨e,hE,hh⟩:=H.heat
  filter_upwards [Baffle.silence B.X B.chip B.A B.a (Z:=B.tour) B.H.laws.intake hE (show Tendsto B.tour (𝓝 0) (𝓝 B.X.V) from B.center.symm ▸ flowJourney 1 B.U) H.cool H.caps H.scales.2 H.scales.1,H.healthy] with x ht hs
  have he:= ht z hz; have hp:=hs z
  have hh': veil B.X B.a B.q u B.b V.D B.A.p d B.A.beta z (B.tour x)=0:= not_not.mp (fun h=> zero_ne_one (he.symm.trans (hp h).1))
  unfold twin Mercury.both Mercury.T6 Mercury.T9 Mercury.box6 Mercury.box9
  change B.pole6 d z x*(coin B.X B.chip B.A B.a d _ _ (B.tour x) z * B.cube M z)-B.pole9 d z x*(veil B.X B.a B.q u B.b V.D B.A.p d B.A.beta z (B.tour x)*B.cube M z)=0; rw [he,hh']; simp only [zero_mul,mul_zero,sub_zero]
lemma salute (z:Prices G B.I)(hz: ‖z‖ ≤ B.tongs)(hv:z∉Prism.outage B.swell): B.OpenKey z ∧ (∀ᶠ x in 𝓝 0,B.honor d u x z):=by
   obtain ⟨p,hp,he⟩:= H.heat; have hh:= H.healthy
   have h:=Prism.seaward B.X B.chip B.A B.a B.q u B.b V.D B.H.laws.intake hp T' H.sph (hh.mono fun p hi s hk=> (hi s hk).1) H.snap.1 H.snap.2 z hz hv
   have hf := h.self_of_nhds
   exact ⟨(hh.self_of_nhds z (ne_of_eq_of_ne hf.2 one_ne_zero)).2,h⟩
lemma wages (z:Prices G B.I):Brush V.n (M.weight*(2* |altitude T' A L κ|)) 1 (fun x=> B.twin M d u x z) 0:=by
   by_cases he:‖z‖ ≤ B.tongs
   · obtain ⟨e,hE,hs⟩:= H.heat
     refine (Mercury.crump B.X B.chip B.A B.a B.q u B.b V.D B.H.laws.intake hE M T' z (H.sph z he)).climb ?_ le_rfl
     apply mul_le_mul_of_nonneg_left _ M.profit; exact mul_le_mul_of_nonneg_left (le_abs_self _) zero_le_two
   exact Brush.zi (B.hush M H z (lt_of_not_ge he)) (mul_nonneg M.profit (by positivity)) zero_le_one
end Barque
end YM.PhysicalNext.Repeat.Sanction
