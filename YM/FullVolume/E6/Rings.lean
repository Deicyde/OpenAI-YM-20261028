import YM.FullVolume.Vision.Score
/-! Ulfa on the comparison.Shadows. not used for choosing cutoffs. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.FullVolume.Shadow
open Function Filter Precision Work OrderedFinpartition Metric
open scoped Topology ContDiff BigOperators Classical
variable {X Y Z : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]{n:ℕ}
variable {μ: Ultrafilter ℕ}{φ:Filter ℕ}{F H K P:ℕ→X→Y}{x:X}{a b:ℕ→Y}
def Glints {ι:Type} [TopologicalSpace ι](φ:Filter ℕ)(F H:ℕ→ι):Prop := ∃ i,Tendsto F φ (𝓝 i) ∧ Tendsto H φ (𝓝 i)
variable {α β γ:Type}[TopologicalSpace α][TopologicalSpace β][TopologicalSpace γ]{f g:ℕ→α}
lemma sails {K:Set α}(h:IsCompact K)(hk:∀ᶠ i in (μ:Filter ℕ), f i∈K): Glints μ f f:=by
    have h' : (↑(μ.map f):Filter α)≤ Filter.principal K:= le_principal_iff.mpr hk
    obtain ⟨x,hx,h⟩:= isCompact_iff_ultrafilter_le_nhds.mp h _ h'; exact ⟨x,h,h⟩
lemma flowers {α:Type}[PseudoMetricSpace α][ProperSpace α]{x:α}{b:ℝ}{f:ℕ→α}(h:∀ᶠ n in (μ:Filter ℕ), dist (f n) x ≤ b):Glints μ f f := sails (isCompact_closedBall x b) h
lemma Glints.bin {Q:α→β}(hf:Glints φ f g)(h:∀ g,Tendsto f φ (𝓝 g)→ ContinuousAt Q g): Glints φ (fun i=> Q (f i)) (fun i=> Q (g i)):=by obtain ⟨u,hu,hx⟩:=hf; exact ⟨_,(h u hu).tendsto.comp hu,(h u hu).tendsto.comp hx⟩
lemma Glints.prods {u v:ℕ→β}{Q:α→β→γ}(hf:Glints φ f g)(he:Glints φ u v)(h:Continuous (uncurry Q)): Glints φ (fun i=> Q (f i) (u i)) (fun i=> Q (g i) (v i)):=by
    obtain ⟨x,hx,h⟩:= (show Glints φ (fun i=>(f i,u i)) (fun i=>(g i,v i)) from by obtain ⟨x,hx,h⟩:=hf; obtain ⟨y,hy,hv⟩:= he; exact ⟨_,hx.prodMk_nhds hy,h.prodMk_nhds hv⟩).bin (Q:=uncurry Q) (fun _ _=> h.continuousAt); exact ⟨x,hx,h⟩
lemma Glints.fibers {ι:Type}{α:ι→Type}[∀ i,TopologicalSpace (α i)]{f g:ℕ→∀ i,α i}(h:∀ i,Glints φ (fun n=> f n i) (fun n=>g n i)):Glints φ f g:=by choose C ha hb using h; exact ⟨C,tendsto_pi_nhds.mpr ha, tendsto_pi_nhds.mpr hb⟩
lemma Glints.carve {u v:ℕ→α}(h:Glints φ f g)(he:f=ᶠ[φ] u)(hp:g=ᶠ[φ] v):Glints φ u v:=by obtain ⟨x,hx,hv⟩:=h; exact ⟨x,hx.congr' he,hv.congr' hp⟩
lemma Glints.every {ι:Type}{f g:ℕ→ι→Y}(s:Finset ι)(h:∀ i∈s,Glints φ (fun n=>f n i) (fun n=> g n i)): Glints φ (fun n=>∑ i∈s,f n i) (fun n=>∑ i∈s,g n i):=by
   choose! u hu hh using h; exact ⟨_,tendsto_finsetSum s hu,tendsto_finsetSum s hh⟩
lemma Glints.shrank (h:Glints φ a b): Tendsto (fun n=> a n-b n) φ (𝓝 0):=by obtain ⟨x,h,hx⟩:=h; exact sub_self x ▸ (h.sub hx)
lemma Glints.time (h:Glints φ a a)(he:Tendsto (fun n=> a n-b n) φ (𝓝 0)): Glints φ a b:=by
   obtain ⟨x,hx,-⟩:=h; have h':Tendsto (fun n=> a n-(a n-b n)) φ (𝓝 (x-(0:Y))):=hx.sub he; exact ⟨x,hx,by simpa using h'⟩
structure Frill (φ:Filter ℕ)(n:ℕ)(x:X)(F H:ℕ→X→Y):Prop where
    seer:∀ᶠ i in φ,ContDiffAt ℝ n (F i) x
    sails:∀ᶠ i in φ,ContDiffAt ℝ n (H i) x
    feel:∀ k:ℕ,k≤n→Glints φ (fun i=> iteratedFDeriv ℝ k (F i) x) (fun i=>iteratedFDeriv ℝ k (H i) x)
variable {f g:ℕ→ℝ}
namespace Frill
lemma crest (h:Frill φ n x F H): Glints φ (fun n=> F n x) (fun n=>H n x):=by
    have H':=(h.feel 0 (Nat.zero_le _)).bin (Q:=ContinuousMultilinearMap.apply ℝ _ Y (0:Fin 0→X)) (fun _ _=>  (ContinuousLinearMap.continuous _).continuousAt); simpa only [ContinuousMultilinearMap.apply_apply, iteratedFDeriv_zero_apply] using H'
lemma bare (h:Glints φ a b): Frill φ n x (fun i _=> a i) (fun i _=> b i) :=by
    refine ⟨Eventually.of_forall fun _=>contDiffAt_const,Eventually.of_forall fun _=>contDiffAt_const,fun k hk=>?_⟩
    cases k with
    | zero => simp_rw [iteratedFDeriv_zero_eq_comp,Function.comp_apply]; exact h.bin (fun _ _=> LinearIsometryEquiv.continuousAt _)
    | succ k=> simp_rw [iteratedFDeriv_succ_const]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
lemma still (y:Y):Frill φ n x (fun _ _=>y) (fun _ _=>y):= bare ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
lemma alter (h:Frill φ n x F H)(he:∀ᶠ i in φ,F i=ᶠ[𝓝 x] K i)(hv:∀ᶠ i in φ,H i=ᶠ[𝓝 x] P i):Frill φ n x K P:=⟨(h.seer.and he).mono fun i hi=> hi.1.congr_of_eventuallyEq hi.2.symm,(h.sails.and hv).mono fun i hi=> hi.1.congr_of_eventuallyEq hi.2.symm,fun k hk=> (h.feel k hk).carve (he.mono fun i hi=> (hi.iteratedFDeriv ℝ k).self_of_nhds) (hv.mono fun i hi=> (hi.iteratedFDeriv ℝ k).self_of_nhds)⟩
lemma fares {Q:Y→Z}(h:Frill φ n x F H)(hb:∀ g,Tendsto (fun i=>F i x) φ (𝓝 g) → ContDiffAt ℝ n Q g):Frill φ n x (fun k y=> Q (F k y)) (fun k y=> Q (H k y)) :=by
    obtain ⟨g,hg,h'⟩:=h.crest; have hp:=hb g hg
    have ht:= hp.eventually (by simp); have hA:= (hg.eventually ht).and h.seer; have hB:=(h'.eventually ht).and h.sails
    refine ⟨hA.mono fun k hk=>hk.1.comp x hk.2,hB.mono fun k hk=>hk.1.comp x hk.2,fun k hk=>?_⟩
    have hx : (k:WithTop ℕ∞) ≤ n:=by exact_mod_cast hk
    let hr p (V:ℕ→X→Y):= fun i=>(p:OrderedFinpartition k).compAlongOrderedFinpartitionL ℝ X Y Z (iteratedFDeriv ℝ p.length Q (V i x)) (fun j=> iteratedFDeriv ℝ (p.partSize j) (V i) x)
    -- placeholder carry inference
    have hh (p: OrderedFinpartition k): Glints φ (hr p F) (hr p H):=by
           let D(Y':ℕ→X→Y)(i:ℕ)(j:Fin p.length):= iteratedFDeriv ℝ (p.partSize j) (Y' i) x
           have hD: Glints φ (D F) (D H):= Glints.fibers fun j=> h.feel _ ((p.partSize_le j).trans hk)
           let V(Y':ℕ→X→Y)(i:ℕ):= iteratedFDeriv ℝ p.length Q (Y' i x)
           have hC:= hp.continuousAt_iteratedFDeriv (k:=p.length) (le_trans (by exact_mod_cast p.length_le) hx);
           have hV: Glints φ (V F) (V H):= ⟨_,hC.tendsto.comp hg, hC.tendsto.comp h'⟩
           exact hV.prods hD (Q:=fun A U=> (p.compAlongOrderedFinpartitionL ℝ X Y Z A) U) (p.compAlongOrderedFinpartitionL ℝ X Y Z).continuous_uncurry_of_multilinear
    exact (Glints.every Finset.univ fun p _=> hh p).carve (hA.mono fun i hi=> (iteratedFDeriv_comp hi.1 hi.2 hx).symm) (hB.mono fun i hi=> (iteratedFDeriv_comp hi.1 hi.2 hx).symm)
lemma via {Q:Y→Z}(h:Frill φ n x F H)(he:ContDiff ℝ n Q): Frill φ n x (fun i x=>Q (F i x)) (fun i x=> Q (H i x)) := h.fares fun _ _=> he.contDiffAt
lemma add (h:Frill φ n x F H)(he:Frill φ n x K P): Frill φ n x (fun i x=>F i x+K i x) (fun i x=> H i x+P i x):=by
    have hx:= h.seer.and he.seer; have hv:= h.sails.and he.sails
    refine ⟨hx.mono fun i hi=>hi.1.add hi.2,hv.mono fun i hi=>hi.1.add hi.2,fun k hk=>?_⟩; have hh : (k:WithTop ℕ∞)≤ n:=by exact_mod_cast hk
    refine (((h.feel k hk).prods (he.feel k hk) (Q:=fun u v=>u+v) (continuous_add)).carve (hx.mono ?_) (hv.mono ?_)); all_goals exact fun i hi=> (iteratedFDeriv_add_apply (hi.1.of_le hh) (hi.2.of_le hh)).symm
lemma twins {K P:ℕ→ X→ Z}(h: Frill φ n x F H)(he:Frill φ n x K P): Frill φ n x (fun i x=>(F i x,K i x)) (fun i x=>(H i x,P i x)):=by
    have H:=h.via (Q:=ContinuousLinearMap.inl ℝ Y Z) (ContinuousLinearMap.inl ℝ Y Z|>.contDiff)
    have H':=he.via (Q:=ContinuousLinearMap.inr ℝ Y Z) (ContinuousLinearMap.inr ℝ Y Z|>.contDiff); refine (H.add H').alter ?_ ?_ <;> filter_upwards with i <;> filter_upwards with x <;> first|exact (Prod.mk_add_mk ..).trans (by simp)
lemma combines {K P:ℕ→X→Z}{Z':Type}[NormedAddCommGroup Z'][NormedSpace ℝ Z'](h:Frill φ n x F H)(hx:Frill φ n x K P){f:Y→Z→Z'}(he:ContDiff ℝ n (uncurry f)): Frill φ n x (fun i x=> f (F i x) (K i x)) (fun i x=> f (H i x) (P i x)):= (h.twins hx).via he
lemma neg (h: Frill φ n x F H): Frill φ n x (fun i x=> -F i x) (fun i x=> -H i x):= h.via contDiff_neg
lemma sub (h:Frill φ n x F H)(he:Frill φ n x K P): Frill φ n x (fun i x=>F i x-K i x) (fun i x=> H i x-P i x):= h.combines he (f:=fun a b=>a-b) (contDiff_fst.sub contDiff_snd)
lemma times {F H K P:ℕ→X→ℝ}(h:Frill φ n x F H)(he:Frill φ n x K P): Frill φ n x (fun i x=> F i x*K i x) (fun i x=> H i x*P i x):= h.combines he contDiff_mul
lemma inn {Y:Type}[NormedAddCommGroup Y][InnerProductSpace ℝ Y]
    {F H K P:ℕ→ X→Y}(h:Frill φ n x F H)(he:Frill φ n x K P) : Frill φ n x (fun i x=> inner ℝ (F i x) (K i x)) (fun i x=> inner ℝ (H i x) (P i x)):= h.combines he contDiff_inner
lemma fee {i :ℕ→X→ℝ} {v:ℕ→X→ℝ} (h:Frill φ n x i v)(he:Frill φ n x F H): Frill φ n x (fun j x=> i j x • F j x) (fun j x=> v j x • H j x):= h.combines he contDiff_smul
lemma buds {ι:Type}{F H:ℕ→X→ι→Y}(s:Finset ι)(h:∀ i∈s,Frill φ n x (fun j x=> F j x i) (fun j x=> H j x i)):Frill φ n x (fun j x=>∑ i∈ s,F j x i) (fun j x=>∑ i∈ s,H j x i):=by
    induction s using Finset.induction_on with
    | empty=> simpa only [Finset.sum_empty] using (still (x:=x) (n:=n) (φ:=φ) (0:Y))
    | @insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (h i (Finset.mem_insert_self ..)).add (ih fun i hj=> h i (Finset.mem_insert_of_mem hj))
lemma pears {ι:Type}{F H:ℕ→X→ι→ℝ}(s:Finset ι)(h:∀ i∈s,Frill φ n x (fun j x=> F j x i) (fun j x=> H j x i)):Frill φ n x (fun j x=>∏ i∈ s,F j x i) (fun j x=>∏ i∈ s,H j x i):=by
    induction s using Finset.induction_on with
    | empty=> simpa only [Finset.prod_empty] using (still (x:=x) (n:=n) (φ:=φ) (1:ℝ))
    | @insert i s hi ih=> simp_rw [Finset.prod_insert hi]; exact (h i (Finset.mem_insert_self ..)).times (ih fun i hj=> h i (Finset.mem_insert_of_mem hj))
lemma stocks {ι:Type} [Fintype ι]{F H:ℕ→X→ι→Y}(h:∀ i:ι, Frill φ n x (fun j y=> F j y i) (fun j y=> H j y i)):Frill φ n x F H:=by
    let L i:= ContinuousLinearMap.single ℝ (fun _ :ι=>Y) i
    refine (buds Finset.univ fun i _=> (h i).via (Q:=L i) (L i|>.contDiff)).alter ?_ ?_
    all_goals filter_upwards with j; filter_upwards with y; ext p; simp [L]
lemma cross {ι:Type}[Fintype ι]{F H:ℕ→ X→ι→Y}(h:Frill φ n x F H)(i:ι):Frill φ n x (fun j y=> F j y i) (fun j y=> H j y i):= h.via (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ :ι=>Y) i|>.contDiff)
lemma reserve (h:∀ᶠ i in (μ:Filter ℕ),ContDiffAt ℝ n (F i) x)(b:ℕ→ℝ)(hx:∀ k,k≤n→ ∀ᶠ i in (μ:Filter ℕ), ‖iteratedFDeriv ℝ k (F i) x‖≤ b k)[FiniteDimensional ℝ X][FiniteDimensional ℝ Y]: Frill μ n x F F:=by
    refine ⟨h,h,fun k hk=>?_⟩
    letI : ProperSpace _:= (show ProperSpace (Tensor.T X Y k) from FiniteDimensional.proper ℝ _)
    exact flowers (x:=0) ((hx k hk).mono fun i hi=>by simpa using hi)
end Frill
end YM.FullVolume.Shadow
