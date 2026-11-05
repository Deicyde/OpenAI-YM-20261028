import YM.TraceExtension.Filch.Choir
import YM.Extra.WILSON_STARTUP.Curvature
import YM.Planned.PRIMARY_INTEGRAL_295.Drupes
set_option autoImplicit false
/-! # outer polynomial color. Not a license for a plog consumption outside marked cube. Only supplies compact globally analytic *germ* representatives and actual conjugation for them. -/
noncomputable section
namespace YM.Trace.Filch
open Function Filter Set Lattice Precision Exterior Stationary Push.Uniform Planned.PrimaryIntegral295.Drupes Lamp Perfect WilsonStartup
open scoped Topology ContDiff Classical Matrix.Norms.Frobenius
variable {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]{G:Gauge}{n d:ℕ}{x:X}

private lemma Kturn (u:G.El)(x:G.Color): localK G (G.adjoint u x)=G.adjoint u (localK G x):=by rw [localK,adjoint_exp,G.curvature_conjugate];rfl
lemma undone (u:G.El): undo G ∘ G.adjoint u=ᶠ[𝓝 0] G.adjoint u ∘ undo G:=by
    let L:= (G.adjoint u).toContinuousLinearMap
    have hp: Tendsto (L ∘ undo G) (𝓝 0) (𝓝 0):=by simpa using! (L.continuous.continuousAt.comp (x:=0) (undo_analytic G).continuousAt).tendsto
    filter_upwards [hp.eventually (undo_left G), undo_right G] with x hx hv
    change undo G (localK G (G.adjoint u (undo G x)))=_ at hx; rw[Kturn, hv] at hx; exact hx

def nimbus(G:Gauge)(n:ℕ)(u:G.El):G.Color:= choral n (undo G) (G.curvature u)
lemma altoM (u y:G.El)(n:ℕ): nimbus G n (u*y*u⁻¹)=G.adjoint u (nimbus G n y):=by
    unfold nimbus; rw[G.curvature_conjugate]; let L:=(G.adjoint u).toContinuousLinearMap
    exact (intoned L (L ∘ undo G) (undo G) (undone u).symm _ (undo_analytic G) _|>.symm).trans (slice_tone L _ n (undo_analytic G) (G.curvature y))
lemma radiant (u:X→G.El)(a:X)(h:ContDiffAt ℝ ω (G.mat ∘ u) a)(n:ℕ): ContDiffAt ℝ ω (nimbus G n ∘ u) a:= (rhythm ..).contDiffAt.comp a (Next.Fluctuations.curvature_diff_mat u a h)
lemma prophet (G:Gauge)(n k:ℕ):∃ C:ℝ,0≤C∧ ∀ (X:Type) [NormedAddCommGroup X] [NormedSpace ℝ X](U:X→ G.El)(R:ℝ)(x:X),Allows k (G.mat ∘ U) x R → Allows k (nimbus G n ∘ U) x (composeCost k C R):=by
    let Z:=choral n (undo G) ∘ cbr G
    obtain ⟨C,hC,H⟩:=exists_allows (f:=Z) (isCompact_range (f:=G.mat) G.continuous_mat) (fun x _=> ((rhythm (undo G) n).comp (cbr G).contDiff).contDiffAt) k
    refine ⟨C,hC,?_⟩; intro T _ _ U r x h
    refine ((H (G.mat (U x)) (mem_range_self ..)).comp (f:= G.mat ∘ U) h).germ ?_
    filter_upwards with y; exact congr_arg (choral n (undo G)) (identifies (U y)).symm
lemma rain_wet (G:Gauge)(n:ℕ): braid id (nimbus G n ∘ G.lieExp) 0 n:= by
    exact (braided (F:=undo G ∘ localK G) (H:=id) (undo_left G)|>.symm).trans (wove (a:=0) (w:=localK G) (show braid (undo G) (choral n (undo G)) _ _ from (localK_zero G).symm ▸ repitch (undo_analytic G) _) ((localK_zero G).symm ▸ undo_analytic G) (rhythm _ n|>.contDiffAt) (localK_analytic G 0))
lemma rain_zero (G:Gauge)(n:ℕ): nimbus G n 1=0:=by
    have hp:= DFunLike.congr_fun (rain_wet G n 0 (Nat.zero_le _)) 0; simpa [iteratedFDeriv_zero_apply] using hp.symm
lemma resounds (U:X→G.El)(h:U 0=1)(hm:ContDiffAt ℝ ω (G.mat ∘ U) 0) (n:ℕ): braid (G.plog ∘ G.mat ∘ U) (nimbus G n ∘ U) 0 n:=by
    have h0:ContinuousAt U 0:= (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.continuousAt_iff.mpr hm.continuousAt
    let T:= G.plog ∘ G.mat ∘ U; have hz:T 0=0:=by simp[T,h]
    have ht:ContDiffAt ℝ ω T 0:=ContDiffAt.comp 0 (g:=G.plog) (by simp only[comp_apply,h,G.mat_one]; exact G.plog_diff) hm
    have hb:= wove (a:=0) (w:=T) (hz.symm ▸ rain_wet G n) contDiffAt_id (radiant _ (T 0) G.exp_jet.contDiffAt _) ht
    apply hb.trans (braided ?_)
    filter_upwards [(show Tendsto U _ (𝓝 1) from h ▸ h0.tendsto).eventually G.plog_right] with z hz; exact congr_arg (nimbus G n) hz
end YM.Trace.Filch
