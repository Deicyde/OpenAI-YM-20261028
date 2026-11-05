import YM.UVExtension.Beach.Cicada
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction MeasureTheory
open scoped Topology BigOperators Classical ContDiff
variable {a:ℝ} (ha:0<a)
local notation "V"=> Row a
local notation "Z"=> ball (0:ℂ) a
variable {n:ℕ}(S:Schedule)(p:ℕ)
variable {F:ℕ→ ℂ→ Tabletop n→ℂ} {f:ℂ→ Points n→ℂ} (t:Test n)
def crumbs (F:ℕ→ ℂ→ Tabletop n→ℂ) (t:Test n)(N:ℕ)(z:ℂ)(r: Fin n→ Site (S.side N p)):= let x:= fun i=>lift (r i); t (tag (S.a N) x) * F N z x
def glass (F:ℕ→ ℂ→ Tabletop n→ℂ) (t:Test n)(N:ℕ)(z:ℂ):ℂ:= (S.a N:ℂ)^(4*n) * ∑ r, crumbs S p F t N z r
local notation "Y"=> NoHit S p n
local notation "X"=> tsupport t
variable (h:suitable S p t)(hf:∀ᶠ i in atTop,∀ x:Tabletop n,DifferentiableOn ℂ (fun z=> F i z x) (Metric.ball (0:ℂ) a))(hm: ∀ K:Set (Points n),K⊆NoHit S p n→ IsCompact K→∃ M:ℝ,0 ≤ M ∧∀ᶠ i in atTop,∀ z∈Metric.ball (0:ℂ) a,∀ x:Tabletop n,Extraction.tag (S.a i) x∈K→ ‖F i z x‖ ≤ M)(hp:Stamp a (NoHit S p n) f (rails S F []))
private lemma plotted (x:Points n)(hx:x∈Fund S p n)(z:ℂ)(N:ℕ): stair S (crumbs S p F t N z) x=t (Extraction.tag (S.a N) (Extraction.address (S.a N) x))* F N z (Extraction.address (S.a N) x):=by
    rw [stair,Set.indicator_of_mem hx]; unfold crumbs; dsimp only; rw [show (fun i=> lift (bucket (S:=S) N p x i))= _ from (show Extraction.address (S.a N) x=(fun i=> lift (bucket (S:=S) N p x i)) from found hx).symm]
include ha h hm hp hf
lemma spectre : AnalyticOnNhd ℂ (fun z=> t.applyTo (f z)) Z ∧ (∀ z:ℂ,z∈ Z → Integrable (fun x=> t x*f z x)) ∧∀ j:ℕ, TendstoLocallyUniformlyOn (fun i=>iteratedDeriv j (glass S p F t i)) (iteratedDeriv j (fun z=> t.applyTo (f z))) atTop Z:= by
    let G(i:ℕ) z:= stair S (crumbs S p F t i z); obtain ⟨u,hU,hB⟩:= hm X (readable S p t h) t.hasCompactSupport;
    obtain ⟨R,hR,ht⟩:= Order.testSup t
    let B:= (Fund S p n).indicator (fun _=> R*u); have hI: Integrable B:= (integrable_indicator_iff (full_box _ _ _).1).mpr (integrableOn_const (full_box _ _ _).2.ne)
    have he : ∀ᶠ i in atTop,∀ z∈Z,∀ x, ‖G i z x‖ ≤ B x:= by
        filter_upwards [hB] with i hi z hz x; by_cases he:x∈Fund S p n
        · rw [show G i z x= _ from plotted S p t x he z i, show B x=R*u from Set.indicator_of_mem he _]; rw [norm_mul]; by_cases hX:t (tag (S.a i) (address (S.a i) x))=0; · rw [hX,norm_zero,zero_mul]; exact mul_nonneg hR hU
          exact mul_le_mul (ht _) (hi z hz _ (subset_closure hX)) (norm_nonneg _) hR
        unfold G B stair; rw [indicator_of_notMem he, indicator_of_notMem he,norm_zero]
    have ht(z)(hz:z∈Z)(x:Points n): Tendsto (fun i=>G i z x) atTop (𝓝 (t x*f z x)):=by
        by_cases hx:x∈Fund S p n; swap
        · have he : t x=0:= by by_contra hT; have he:= h (subset_closure hT); exact hx fun i a=> ⟨(he i a).1,(he i a).2.le⟩
          unfold G stair; simp_rw [indicator_of_notMem hx,he,zero_mul]; exact tendsto_const_nhds
        unfold G; simp_rw [plotted S p _ x hx]; let y(i):= address (S.a i) x
        have hy : Tendsto (fun i=> tag (S.a i) (y i)) atTop (𝓝 x):= chosen x
        by_cases H:x∈ tsupport t
        · have hv : x∈Y:= Extraction.readable S p t h H
          refine (t.continuous.continuousAt.tendsto.comp hy).mul ?_; apply Metric.tendsto_nhds.mpr; intro ε hε; have hf := hp.converges _ isCompact_singleton (Set.singleton_subset_iff.mpr hz) _ isCompact_singleton (Set.singleton_subset_iff.mpr hv) 0 ε hε
          filter_upwards [hf] with i hi; rw [dist_eq_norm]; simpa only [iteratedDeriv_zero, rails,Ink,rake] using! hi z rfl x rfl
        have hh :t x=0:= by_contra fun h=> H (subset_closure h); rw [hh,zero_mul]; apply (Tendsto.congr' ?_ (tendsto_const_nhds (x:=(0:ℂ))))
        filter_upwards [hy.eventually ((isClosed_tsupport (f:=t)).isOpen_compl.mem_nhds H)] with i hi; exact (show _ = (0:ℂ) from mul_eq_zero_of_left (by_contra fun hx=> hi (subset_closure hx)) (F i z (y i))).symm
    have hp'(i:ℕ)(z): Integrable (G i z):= stair_int _; have hv(z)(hz:z∈ Z): Integrable (fun x=> t x*f z x)∧ Tendsto (fun i=> glass S p F t i z) atTop (𝓝 (t.applyTo (f z))):=by
        let g z x:= t x*f z x; have hh':∀ᵐ x:Points n,Tendsto (fun i=> G i z x) atTop (𝓝 (g z x)):= Eventually.of_forall (ht z hz)
        have hk:Integrable (g z):= hI.mono' (aestronglyMeasurable_of_tendsto_ae atTop (fun n=> hp' n z|>.aestronglyMeasurable) hh') (hh'.mono fun x hx=> le_of_tendsto hx.norm (he.mono fun i hi=> hi z hz x))
        exact ⟨hk,(tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall (fun n=> hp' n z|>.aestronglyMeasurable)) (he.mono fun i hi=>Eventually.of_forall (hi z hz)) hI hh').congr' (Eventually.of_forall (fun i=> stair_integral _))⟩
    obtain ⟨n,hN⟩:= eventually_atTop.mp (hf.and he); let M:= max 1 (∫ x,B x); let f'(i:ℕ):= if i≥n then glass S p F t i else fun _=>0; have hp'': ∀ᶠ i:ℕ in atTop, f' i= glass S p F t i:= (eventually_ge_atTop n).mono fun i hi=> if_pos hi
    have hh(i): DifferentiableOn ℂ (f' i) Z∧ ∀ z∈ Z, ‖f' i z‖ ≤M:=by
       unfold f'; split
       next h=> refine ⟨DifferentiableOn.const_mul (DifferentiableOn.fun_sum (fun j _=> DifferentiableOn.const_mul (hN i h|>.1 _) _)) _,fun z hz=>?_⟩; exact (le_trans (show ‖glass S p F t i z‖ ≤ ∫ x,B x from by rw [glass,← stair_integral (crumbs S p F t i z)]; exact (norm_integral_le_integral_norm _).trans (integral_mono ((hp' i z).norm) hI ((hN _ h|>.2) _ hz))) (le_max_right ..))
       next=> exact ⟨differentiableOn_const _,fun z hz=> norm_zero.trans_le (zero_le_one.trans (le_max_left ..))⟩
    obtain ⟨G',hG,hH⟩:= Camp.viva a ha M hh (fun x hx=> let z:Row a:=⟨x,hx⟩; ⟨_, (hv _ (desk a ha|>.within z)|>.2).congr' (hp''.mono (fun i hi=> congr_fun hi.symm (x:ℂ)))⟩) -- Lean let hx. result
    have hS : EqOn G' (fun z=> t.applyTo (f z)) Z:= by
       have hh': TendstoLocallyUniformlyOn f' G' atTop Z:=by simpa using! hH 0
       exact fun z hz=> tendsto_nhds_unique ((hh'.tendsto_at hz).congr' (hp''.mono fun i hi=> congr_fun hi z)) (hv z hz|>.2)
    refine ⟨((hG.differentiableOn.congr hS.symm).analyticOnNhd isOpen_ball),fun z hz=> hv z hz|>.1,fun j=>?_⟩; have hp(j):=hH j
    have he:(fun i=>iteratedDeriv j (glass S p F t i))=ᶠ[atTop] fun i=>iteratedDeriv j (f' i):=hp''.mono fun i hi=>congr_arg (iteratedDeriv j) hi.symm
    refine (((hp j).congr_inseparable (G:=fun i=>iteratedDeriv j (glass S p F t i)) (he.mono ?_)).congr_right (fun z hz=>?_))
    · intro i hi v hv; rw [show iteratedDeriv j (glass S p F t i) v=iteratedDeriv j (f' i) v from congr_fun hi v]
    exact (show G'=ᶠ[𝓝 z] _ from Eventually.mono (p:=fun v=>v∈ Z) (isOpen_ball.mem_nhds hz) (fun _ hx=>hS hx)).iteratedDeriv_eq j
end YM.UVExtension.Beach
