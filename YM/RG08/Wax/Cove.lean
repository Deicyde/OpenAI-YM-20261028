import YM.RG08.Wax.Parade
/-! # Lift coincidences even on stencils. No cycle discarded without proof.
Period arrays for normalization not claimed identical before cover. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Wax
open Function Filter Finset RG Stationary Quire Shade Bands Analysis Laurent Lattice Bloch Next.Free
open scoped Topology ContDiff BigOperators Matrix Classical
variable {I X:Type} [DecidableEq I] [Fintype X] [DecidableEq X] {m:ℕ→Side}{p : Option Side}{K:Bloch.Row X X}{S:Canticle X}
variable {a:I→ℕ}{F:Topaz I (Screed ℝ X)} {U : ℕ→ Topaz I (HeatS X)} {V : Topaz I (HeatS X)}
lemma tips_sum {Z: Type} {U : Z → ℕ→ HeatS X} {V:Z→ HeatS X}(f:Finset Z)(h:∀ i∈f,Tips (U i) (V i)) : Tips (fun n=>∑ i∈f,U i n) (∑ i∈f,V i):= by
    intro i j k; simp_rw [Finset.sum_apply]; exact Hurled.additions f fun i hi=> h i hi ..
lemma tips_sm {V:HeatS X}{U:ℕ→HeatS X}(h:Tips U V)(s:ℝ):Tips (fun i=>s • U i) (s • V):= fun i j k=> (h i j k).scale s
lemma tipLever (h:∀ t:Finset I,Tips (fun i=>U i t) (V t)) (hp:Whole K)(he:Gets S)(hk:Tendsto (fun i=>(m i).val) atTop atTop) (t) : Tips (fun i=>lever (some (m i)) K S (U i) t) (lever none K S V t):= by
    exact tips_more (F:=fun i=> pumpP (some (m i)) K S (U i t)) (Q:=fun i=> (1/2:ℝ) • arches (some (m i)) K (U i) (U i) t) (tips_peel hp he hk (h t)) (tips_sm (U:=fun i=> arches (some (m i)) K (U i) (U i) t) (tips_sum (U:=fun (p:Finset I× Finset I) i=> thunder (some (m i)) K (U i p.1) (U i p.2)) _ (fun i _=>tips_t (h i.1) (h i.2) hp hk)) _)
lemma pulse_tips (hp:Whole K)(h:Gets S)(hf:∀ i,Sails (vanes a i) (F i))(he:Tendsto (fun i=>(m i).val) atTop atTop)(t:Finset I): Tips (fun i=> pulse (some (m i)) K S F t) (pulse none K S F t) := by
    intro n; induction n using Nat.caseStrongRecOn generalizing t with
    | zero=> intro i j; simp_rw [pulse_z]; exact Hurled.fixed ((hf t).tide i j|>.pens)
    | ind n ih=>
      let K' p t:=fun i=> if h:i≤n then pulse p K S F t i else 0
      have ht p k : pulse p K S F k (n+1)=((↑(n+1:ℕ)):ℝ)⁻¹ • lever p K S (K' p) k n:= by rw [pulse]
      have hT (t): Tips (fun i=> K' (some (m i)) t) (K' none t):= by
        intro b j k; by_cases hp:b≤n; · simp only [K',dif_pos hp]; exact ih b hp t j k
        simp only [K',dif_neg hp,Pi.zero_apply]; exact Hurled.fixed (Pens.zero ..)
      intro i j; simp_rw [ht,Pi.smul_apply]; exact (tipLever hT hp h he _ n i j).scale _
lemma tips_ban (h : ∀ t: Finset I,Tips (fun i=>U i t) (V t)) (t:Finset I) : Tips (fun i=>banner t (U i) borne (upstart X)) (banner t V borne (upstart X)):= by
   induction t using strongInductionOn with
   | _ t ih=>
    by_cases ht:t=∅; · subst t; simp_rw [banner_one]; exact tips_none 0 reels_start
    let b(T:Topaz I (HeatS X))(p:directVote t):= borne (sons T p.val.1) (banner p.val.2 T borne (upstart X))
    have hk (F): banner t F borne (upstart X) = (↑t.card:ℝ)⁻¹ • ∑ i,b F i:= by rw [banner,if_neg ht]
    simp_rw [hk]; apply tips_sm; apply tips_sum (U:=fun i t=> b (U t) i) _; intro p _; exact tips_b (tips_sm (h _) _) (ih _ (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp (mem_product.mp (mem_filter.mp (mem_filter.mp p.property).1).1).2,fun v=>not_lt_of_ge (congr_arg Finset.card v).ge (shrank _ p.property)⟩))
lemma prehistoric (hp:Whole K)(h:Gets S)(hf:∀ i,Sails (vanes a i) (F i))(hx:F ∅=0)(hK:∀ c,(K.acts c)ᵀ=K.acts c)(t:Finset I) :
    banner t (pulse none K S F) borne (upstart X)=murmur none K S (banner t F gust (spine_one X)) := by
   let R:=banner t F gust (spine_one X); have he : Sails (vanes a t) R:=banner_z none hp h hf _
   let L(n:ℕ): Side:=⟨n+1,Nat.succ_pos _⟩; have hv:Tendsto (fun i=>(L i).val) atTop atTop:= tendsto_add_atTop_nat _
   apply relic (m:=L) (tips_ban (U:=fun i=> pulse (some (L i)) K S F) (pulse_tips hp h hf hv) t) (walksR (pulse_ok F hp h hf) _) (W:=fun i=> murmur (some (L i)) K S R) ?_ (dressing he hp h) (fun i=> walksR (pulse_ok _ hp h hf (p:=some (L i))) t) (fun i=> dressing he hp h) hv (fun i=> page_rose hp h (hK (L i)) hf hx (0:Site (L i)) t)
   exact fun i j k=> Hurled.furs (U:=fun _=>R) L (fun i j=> Hurled.fixed (he.tide i j|>.pens)) h hp hv ..
end YM.RG08.Wax
