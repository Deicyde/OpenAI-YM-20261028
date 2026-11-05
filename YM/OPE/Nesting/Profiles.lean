import YM.OPE.Nesting.Integration

/-! The uniform estimates not just for products of individual test
profiles, but jointly variable placements of all centers, leaves,
exterior points and the viewer. Character mixing on the original
hierarchy means taking its probability-integrated moments (indeed
these are readable by the SAME finite coefficient sum which does
not vary with that character). -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset TopologicalSpace
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Tree
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)

section Clip
variable {I J:Type}[Fintype I][Fintype J]{d:I→ℕ}{e:J→ℕ}(v:Labels S d)(w:Labels S e)
private lemma clip_whole (m:ℕ) (r:Viewers U):
       Measurable ((guardZone U R m).indicator (fun z:Loc I J=>whole (spectator U r) z.1 v z.2.2 w)):=
    by have hc:=show ContinuousOn (fun z:Loc I J=>whole (spectator U r) z.1 v z.2.2 w) (guardZone U R m) from (fun x hx=> (Orbits.whole_cont_at v w (spectator U r) (spectate U r) (x:=x) (hx.2.1)).continuousWithinAt)
       convert hc.measurable_piecewise (continuousOn_const (c:=(0:ℂ))) (guard_open U R m|>.measurableSet) using 1
       ext i; by_cases hi:i∈guardZone U R m <;> simp [Set.indicator,Set.piecewise,hi]

private lemma clip_mixed (m:ℕ): Measurable (fun x:Loc I J × U.α.space.X=> (guardZone U R m).indicator (fun z:Loc I J=>whole (U.α.ensemble x.2) z.1 v z.2.2 w) x.1) :=by
   let f(r:U.α.space.X)(z:Loc I J):= whole (U.α.ensemble r) z.1 v z.2.2 w
   letI : Nonempty U.α.space.X := ⟨U.α.atPoint⟩
   refine measurable_mixed (f:=fun r=> (guardZone U R m).indicator (f r)) ?_ (fun r=>clip_whole U R v w m (some r))
   intro z
   by_cases hi:z∈guardZone U R m
   · simp only [indicator_of_mem hi]
     have h:=U.phase.phase.decomposition.weak (viewing U (beside z.1 z.2.2) (beside (names v) (names w)))
     exact h.congr (fun i=> (character_sees U i _ _ hi.2.1).trans ((whole_observed ..).symm))
   simp only [indicator_of_notMem hi]; exact continuous_const
end Clip

variable {K J:Type}[Fintype J][MeasurableSpace K]
variable (h:Services C F S){M η ε δ:ℝ}(hM:0≤M)(hη:0<η)(hε:0<ε)(hδ:0<δ)
variable {n:ℕ}{f:Fin n→Tree}
       (v:(fork n f).Leaf→S.Tag)(w:J→S.Tag)(m:ℕ)

def TestedProfile (t:Tree)(z:Tree.Envelope K t)(y:K→J→E4): K→ Loc t.Leaf J:= fun i=>Kernel.cardPanel (z i) (y i)

include h hM hη hδ hε
-- bound uniform over arbitrary placement weights/tests whose total masses are bounded
lemma all_weighted : ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:((fork n f).Inner→ℝ))(μ:Measure K)(B:ℝ)(u:K→ℂ), Tapered (fork n f) r 1 s → Integrable u μ→ (∫ i, ‖u i‖ ∂μ) ≤ B →
    ∀ (z:Tree.Envelope K (fork n f))(y:K→J→E4), AEMeasurable z μ → AEMeasurable y μ → (∀ᵐ i ∂μ,u i≠0→Accept r M η s (z i) ∧ Buffer (z i) (y i) δ) →
    let estimate:=JointEstimate U R m (voices v) (voices w) (B *(Tree.toll (wages v) ε (m+1:ℝ) s) ) μ u (TestedProfile (fork n f) z y)
    (∀ t:K→U.α.space.X, AEMeasurable t μ →estimate (.some ∘ t)) ∧ estimate (fun _=>none):=by
    filter_upwards [raw_wave U R h hM hη hε v w hδ,Limits.tested_power U R h hM hη hδ hε v w m] with r ht he s μ B u hs hf hq z y hz hy H
    let t:=fork n f; let p:K→ Loc t.Leaf J:= TestedProfile t z y
    have hp:AEMeasurable p μ:= ((Kernel.plot_smooth (J:=J) (t:=t)).continuous.measurable).comp_aemeasurable (hz.prodMk hy)
    let b (m:ℝ):= Tree.toll (wages v) ε m s
    let guard:= guardZone (I:=t.Leaf) (J:=J) U R m
    have test {Y:Type}[MeasurableSpace Y] (g:Y→Viewers U)
         (hx:Measurable (fun z:Loc t.Leaf J × Y=> guard.indicator (fun t=> formula U R t.1 t.2.1 (voices v) t.2.2 (voices w) m (g z.2)) z.1))
         (hx':Measurable (fun z:Loc t.Leaf J × Y=> guard.indicator (fun t=> whole (spectator U (g z.2)) t.1 (voices v) t.2.2 (voices w)) z.1))
         (phase:K→Y)(h:AEMeasurable phase μ): JointEstimate U R m (voices v) (voices w) (B*b (m+1)) μ u p (g ∘ phase):=by
           apply price_measurable U R _ _ p phase g m (c:=b (m+1)) (A:=b 0) (B:=B) hx hx' hp h hf hq _ _ _ (hs.pay_nonneg ..)
           · exact H.mono fun i hi hw=>(he s (z i) (y i) (hi hw).1 (hi hw).2).1
           · exact H.mono fun i hi hw=>(he s (z i) (y i) (hi hw).1 (hi hw).2).2.2 (g (phase i))
           exact H.mono fun i hi hw=>(ht s (z i) (y i) (hi hw).1 (hi hw).2) (g (phase i))
    exact ⟨fun y hy=>test (Y:=U.α.space.X) some (mixed_meas ..) (clip_mixed ..) y hy, test (Y:=Unit) (fun _=>none) ((indicator_meas ..).comp measurable_fst) ((clip_whole ..).comp measurable_fst) (fun _=>()) aemeasurable_const⟩

omit [MeasurableSpace K] in
lemma phase_mixtures : ∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:Tree.Plot (fork n f)) (y:J→E4),Accept r M η s z → Buffer z y δ→∀ (μ:Measure U.α.space.X), IsProbabilityMeasure μ → ‖ phaseMoment U (voices v) (voices w) μ (Kernel.cardPanel z y) -phaseSum U R (voices v) (voices w) μ m (Kernel.cardPanel z y)‖ ≤ toll (wages v) ε (m+1:ℝ) s:=by
    filter_upwards [all_weighted (K:=U.α.space.X) U R h hM hη hε hδ v w m, Limits.tested_power U R h hM hη hδ hε v w m] with r h hp s z y he h_c μ hμ
    have ho:=same_in_mixture U R (voices v) (voices w) μ m (Kernel.cardPanel z y) ((hp _ z _ he h_c).1.2.2)
    obtain ⟨-,_,_,ht,hb⟩:=(h s μ 1 (fun _=> (1:ℂ)) he.levels (integrable_const _) (by simp) (fun _=>z) (fun _=>y) aemeasurable_const aemeasurable_const (ae_of_all _ fun _ _=>⟨he,h_c⟩)).1 _ (aemeasurable_id)
    rw [phaseMoment,ho]; simp only [Function.comp_apply,TestedProfile,id_eq,one_mul] at hb ht
    exact ht ▸ hb
end YM.OPE.Nesting
