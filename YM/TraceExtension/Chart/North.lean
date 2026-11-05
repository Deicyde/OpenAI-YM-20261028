import YM.TraceExtension.Chart.Earl
import YM.TraceExtension.Chart.Masts
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Over
open Set Function Filter Analysis MeasureTheory Table Ward Climb Extraction Work Work.A05
open Next.UVStress Labels
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G : Gauge} {C:Family G}{S:Table C.book}{n:ℕ}
open Next.Rank.Price Next.Rank.East MergeProof.East Terrace Shelves Slate UVNext.FreeStress Maxwell Labels
variable {G:Gauge}{C:Family G}{Z:Arch C}{S:Table C.book}(HE:S.Hierarchy) (H:(Climb.Bel C.book).Hierarchy) (h:G.Simple) {U:DiffPlan S}{Y:DiffPlan (Climb.Bel C.book)} (ht:U.Derivatives S)(hv:Y.Derivatives (Climb.Bel C.book))(hu:Y.Orientation H.spin)
include hv hu h in
lemma awake_o : ∃ b:Axis,∃ (o : Work.A05.Observer (Climb.Bel C.book)) (v:(Climb.Bel C.book).Field 4), o.test 5 (Y.deriv 4 b v)≠0:=by
    let F:= Climb.Bel C.book; let f:= Y.deriv 4
    have he := scope_exact C.labels H.spin h Y hv hu
    obtain ⟨x,hx⟩:= he.2 (1,0); have hx':x≠0:=by intro ht; rw [ht,map_zero] at hx; exact zero_ne_one (congr_arg Prod.fst hx)
    by_contra! hf; obtain ⟨J,hJ⟩:= rank_on C.labels H.spin h Y hv hu x
    obtain ⟨s,hs⟩:= Observer.exists_reads H 5
    have hB(b:Axis)(v:F.Field 4): f b v=0:= hs _ _ fun o _=> by rw[map_zero]; exact hf b o v
    apply hx'; rw [← hJ]; refine Subtype.ext (funext fun i=>?_); change ∑ j:Axis,f j (J.val j i) = 0; simp only [hB,Finset.sum_const_zero]
variable {J:Scaling S} (R: Table.Stress S) (hR:Marvel S HE.spin R U)
variable {V:∀ i,Vane C i}
include ht hv hu
-- calibrates stress amplitude; *physical*.
include HE h hR
variable (ho:U.Orientation HE.spin) (hK:ChoiceK HE U ho J V Z) (hp:Approaches (path J) (isoPanel J)) (h':Marvel (Climb.Bel C.book) H.spin (materialB C none) Y)
include hK hp h' ho
lemma year_spec : Tendsto (fun k=>Year J k R) atTop (𝓝 (materialB C none)) ∧
    Tendsto (fun i=>BQ Z V i • ∑ j:Axis, Year J i R j j) atTop (𝓝 ((4*forceR G) • OScale C.book)):=by
    obtain ⟨b,o,v,hg⟩:= awake_o H h hv hu; let F:= Climb.Bel C.book
    obtain ⟨p,hV⟩:= hR.flux; obtain ⟨q,hU⟩:= h'.flux; let y:= o.test 5 (Y.deriv 4 b v); let χ:=o.cut
    have he:shellGrad F (materialB C none) χ b o.x o.q v=y:=by
        rw [hU.translation o.hx o.q o.cut_window]; unfold y Observer.test; rw [frontRead_at];rfl
    let f(k):= (J.r k:ℂ)* shellGrad S R (stretch (J.r k) χ) b (J.r k • o.x) (J.pins k ∘ o.q) (J.U k 4 v)
    have ht(k):Window (J.r k • o.x) (stretch (J.r k) χ):= window_stretch (J.positive k) o.cut_window
    have hB(k):J.r k • o.x∈ conf _:= smul_conf (J.positive k) o.hx
    have hF:Tendsto f atTop (𝓝 y):= (pay_jet HE H U Y hp ‹_› hv 4 b v o).congr (fun i=>by unfold f; rw[hV.translation (hB i) _ (ht i)])
    have hN:R≠0:=by
         intro hK; have hz(i):f i=0:=by
             unfold f; rw[hK,← A15.translationFlux_apply (hB i) (ht i) HE.smooth]; rw[map_zero, mul_zero]
         exact hg (tendsto_nhds_unique_of_eventuallyEq hF tendsto_const_nhds (Eventually.of_forall hz))
    obtain ⟨g,hts,hJ,hY⟩:= hK.intent
    let k₀:= LinearMap.ker (currentDiv U HE.spin ho); let r:KernelSpace HE.spin:=⟨R,hR.currents.1⟩; let R':k₀:=⟨r,(linear_cons U HE.spin ho r).mpr (hR.currents.2)⟩; have hN':R'≠0:=fun hq=>hN (congr_arg (fun v:k₀=>v.val.val) hq)
    let w(k:ℕ):= (g k).val; let T:=materialB C none;
    have hh : ∀ᶠ i:ℕ in atTop, ∃ v:ℝ,w i= v • R:=by filter_upwards [hts] with i hi; obtain ⟨v,hv⟩:= (finrank_eq_one_iff_of_nonzero' R' hN'|>.1 hK.rank) ⟨g i, (linear_cons _ _ _ _).mpr hi⟩; exact ⟨v, (congr_arg (fun t:k₀=> t.val.val) hv).symm⟩
    let v'(i):= if hp:∃ v:ℝ,w i= v • R then hp.choose else 1; have ht':∀ᶠ i in atTop,w i=v' i • R:= hh.mono (fun i hi=>by unfold v'; rw [dif_pos hi]; exact hi.choose_spec)
    obtain ⟨D,N,M,hM,hO⟩:= o.enough 4; have hM':= hO _ le_rfl _ le_rfl _ le_rfl; have hh := comparison_jets HE ‹_› H hv J hp N D 0 M (zero_lt_one.trans_le hM);
    have hV:= drape J HE.smooth H.smooth (T:=T) hJ o.x o.hx o.cut_window b hh hM'.total hM'.stress hM'.ringFits o.q hM'.rest 4 v hM'.stress; rw [he] at hV
    have hf:Tendsto (fun i=>(v' i:ℂ)*f i) atTop (𝓝 y):=by
         refine hV.congr' ?_; filter_upwards[ht'] with i hi
         change (J.r i:ℂ)*shellGrad S (w i) (stretch (J.r i) χ) _ _ _ _=_
         rw [← A15.translationFlux_apply (hB i) (ht i) HE.smooth,hi,RCLike.real_smul_eq_coe_smul (K:=ℂ) (v' i) R,map_smul,A15.translationFlux_apply, smul_eq_mul]; unfold f;exact mul_left_comm _ _ _
    have hq1:Tendsto v' atTop (𝓝 1):=by
        have hu :Tendsto (fun i=>(v' i:ℂ)) atTop (𝓝 1):=by
            have h1 := hf.div hF hg; rw [div_self hg] at h1; exact h1.congr' ((hF.eventually_ne hg).mono fun i hi=>mul_div_cancel_right₀ _ hi)
        exact Complex.continuous_re.continuousAt.tendsto.comp hu
    have hA : ∀ᶠ i in atTop,(v' i)⁻¹ • w i=R:=by
        filter_upwards[ht',hq1.eventually_ne one_ne_zero] with i hi ht
        rw [hi,inv_smul_smul₀ ht]
    have hv:Tendsto (fun i=>(v' i)⁻¹) atTop (𝓝 1):=by simpa using! hq1.inv₀ one_ne_zero
    constructor
    · have he:= hv.smul hJ; rw [one_smul] at he; refine he.congr' (hA.mono fun i hi=>?_ ); change _ • Year J i (w i)=Year J i R; rw[← hi,map_smul]
    have he := hv.smul hY; rw[one_smul] at he; apply he.congr'; filter_upwards [hA] with i hi
    change (v' i)⁻¹ • (BQ Z V i • ∑ j:Axis, Year J i (w i) j j)=BQ Z V i • ∑ j:Axis,Year J i R j j; conv_rhs=> rw[← hi]; rw [map_smul]
    rw [smul_comm (_:ℝ) (BQ Z V i),Finset.smul_sum];rfl
end YM.Trace.Over
