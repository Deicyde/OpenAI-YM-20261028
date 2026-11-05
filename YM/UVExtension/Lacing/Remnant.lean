import YM.UVExtension.Lacing.Discount
import YM.UVExtension.Limits
/-!
 # Persistence test at fixed real step for Crown. Need uniform lower bound and accumulation on each input,
 not just each coefficient clamped. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lacing
open Function Filter MeasureTheory Set Lattice Wilson RG Source Extra.Histories Labels
open Planned.GuardedAtom Guard Push Local MergeProof Motion Next.Foundations
open Bid Concert BoundedContinuousFunction Eyelet RoutesF Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{n n':Side}{d:ℕ} {F:Frame G d}{p P :BudgetPoint}{H:Hol G}{X Ω:Type}
local notation "E"=> Cow G n' p d H
local notation "B"=> Cow G n P d H
local notation "Lc"=> Bucket F P H n
variable [NormedAddCommGroup Ω] [NormedSpace ℂ Ω] [FiniteDimensional ℂ Ω][NormedAddCommGroup X] [NormedSpace ℂ X][CompleteSpace X]
namespace Remnant
lemma portal {f:ℕ→ Ω→L[ℂ] X}(h:∀ i,Arrives fun n=> f n i): Arrives f:=by
   -- finite Dim reconstruct with dual projections. seminorm proof
   let V:= Module.finBasis ℂ Ω
   let U:= fun i x=> V.equivFun x i
   let w i:= ((LinearMap.proj (φ:=fun _=>ℂ) i).comp V.equivFun.toLinearMap).toContinuousLinearMap
   have hw (g:Ω→L[ℂ] X): (∑ i, (w i).smulRight (g (V i)))=g:=by
      apply ContinuousLinearMap.ext; intro x
      simp only [_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
      simp_rw [← map_smul,← map_sum]; exact congr_arg g (V.sum_repr x)
   refine Arrives.copy (Arrives.sum (f:=fun n i=> (w i).smulRight (f n (V i))) Finset.univ (fun i _=>?_)) (Eventually.of_forall fun i=> hw _)
   exact (h (V i)).post ((ContinuousLinearMap.smulRightL ..) _|>.continuous)

lemma traceV {f:ℕ→ Ω→ₗ[ℂ] X}(h:∀ i,Arrives fun n=> f n i) : Arrives (fun n=> (f n).toContinuousLinearMap):=portal h
lemma loops {f:ℕ→ Ω→ₗ[ℂ] X}{x:ℕ→Ω}(h:∀ i,Arrives fun n=> f n i)(hp:Arrives x) : Arrives (fun n=> f n (x n)):= by
   obtain ⟨z,h⟩:= traceV h; obtain ⟨v,hv⟩:=hp; exact ⟨z v,((show Continuous (fun i:(Ω→L[ℂ] X) × Ω=> i.1 i.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (h.prodMk_nhds hv))⟩
lemma solved {Ω:Type} [NormedAddCommGroup Ω] [NormedSpace ℂ Ω][FiniteDimensional ℂ Ω]
    {f:ℕ→ Ω→L[ℂ] Ω}(h:∀ i,Arrives fun n=> f n i) (u:ℝ) (hp:∀ᶠ i in atTop,∀ v, ‖v‖≤ u*‖f i v‖) (x:Ω): Arrives fun i=> (steers (f i)).symm x:=by
   obtain ⟨F,h⟩:= Remnant.portal h; have ht(v): Tendsto (fun i=> f i v) atTop (𝓝 (F v)):= (show Continuous (fun i: Ω→L[ℂ] Ω=> i v) from continuous_eval_const _).continuousAt.tendsto.comp h
   have hh(v): ‖v‖≤ u*‖F v‖:= ge_of_tendsto ((ht v).norm.const_mul _) (hp.mono fun i hi=> hi v)
   have hk(g:Ω→L[ℂ] Ω) (h:∀ v, ‖v‖≤ u*‖g v‖): Bijective g:=by
      let T:=g.toLinearMap; have hh:T.ker=⊥:=by apply LinearMap.ker_eq_bot'.2
                                                intro v hv
                                                apply norm_le_zero_iff.mp; simpa [show g v=0 from hv] using h v
      have he:=LinearMap.ker_eq_bot.mp hh; exact ⟨he,LinearMap.injective_iff_surjective.mp he⟩
   obtain ⟨y,hF⟩:= (hk F hh).2 x
   refine ⟨y,tendsto_iff_dist_tendsto_zero.mpr ?_⟩
   have hY: Tendsto (fun i=>u*‖x-f i y‖) atTop (𝓝 0):=by
       have ht:=ht y
       rw [hF] at ht; simpa using! (tendsto_const_nhds (x:=x)|>.sub ht).norm.const_mul u
   refine squeeze_zero' (Eventually.of_forall fun _=>dist_nonneg) ?_ hY
   filter_upwards [hp] with i hi
   rw [dist_eq_norm]; apply le_trans (hi _)
   rw [map_sub,← steers_eq _ (hk _ hi), LinearEquiv.apply_symm_apply]
end Remnant
end YM.UVExtension.Lacing
