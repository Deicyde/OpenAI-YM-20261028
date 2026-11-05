import YM.Contacts.Harvest.Outer
/-!
# Field-local contact pairing estimates in regulated forests

This class of loans allows root estimators immediately in grades through their running weight
or their corresponding signed residual, paying parent horizons thereby *before* any disjoint
legs also take the branches. More bounds hold than merely pointwise agreement on support: the
total norm with each branch & any shell choices already fixed costs only the small subpowers
(room function at any ε with adequate slack), all aperture shapes, phases, stage tests, etc
controlled as in this API. No constants depend on further a subsequence of parameters. We
supply here the induction theorem. Use with the same Devices for all demands.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Harvest.Route
open Function Filter Set Metric MeasureTheory Submodule Table Spec Normal MultipleContact OPE Layers Ordered
open scoped Topology Classical BigOperators ContDiff InnerProductSpace MeasureTheory
variable {E X W I : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
 [NormedAddCommGroup X][NormedSpace ℂ X] [CompleteSpace X]
variable {G: Gauge} {C: Family G}{F: Extraction.Order}{S : Table C.book} {Z: Final C F S}
variable {k : ℕ} {d : Fin k→ℕ}{g : Normal.Group k} {P : E→ₗᵢ[ℝ] Points k} {Q : Pieces g} {γ : ℝ}
variable (M : Devices Z.sector.derivatives)
variable (r : Route P Q I W) (T : W→ Cells S d) (D : Reader E W X k Z.sector.derivatives)
variable (i : Q.parts) (h : 1 < i.val.card)
include h
omit [CompleteSpace X] in
lemma decomposition (f : Menu k) (w z x) : r.windings M D T f w z x=
    ∑ b∈(r.components M T w).slate i.val (f i.val), r.select M T D i (d:=d) (show Way d i.val from b) f w (System.sliceAt P i.val (f i.val).slice (r.net i b w z)) x := by
   unfold windings scoreAt; rw [System.renewal P (r.length w) (r.components M T w) f Q i h,map_sum]; apply Finset.sum_congr rfl; intro b hb
   unfold select scoreAt net; rw [r.treated,r.core_mask]; rfl

variable [MeasureSpace E][BorelSpace E][(volume:Measure E).IsAddHaarMeasure]
variable [Fintype I] {B : W→ℝ}
omit [BorelSpace E] [(volume:Measure E).IsAddHaarMeasure] [CompleteSpace X] in
lemma all_armed (hB : ∀ w,0<B w) (_hh : Economy Q γ) (h' : ∀ b : Way d i.val,∃ C>(0:ℝ), ∀ f w (z:SmoothTests E)(c:ℝ),tsupport z.val⊆r.stage w → Jet (stairs d Q) univ (composed (r.frame w) z).val c →
     Dust (r.select M T D i b f w (System.sliceAt P i.val (f i.val).slice (r.net i b w z))) (C*c*r.bag d B w (generosity Q γ)*shadow Q f γ)) : ∃ C>(0:ℝ), Achieves Z M r T B D γ C := by
   choose t ht hv using h'; let C:= ∑ i,t i; have hC:0<C:= Finset.sum_pos (fun i _=> ht i) Finset.univ_nonempty; refine ⟨C,hC,?_⟩; constructor; intro f w p c hp h₁; let b:= r.bag d B w (generosity Q γ); let D':=shadow Q f γ
   let q:Finset (Way d i.val):=(r.components M T w).slate i.val (f i.val); let F(x:Way d i.val):=r.select M T D i x f w (System.sliceAt P i.val (f i.val).slice (r.net i x w p)); rw [show r.windings M D T f w p =(fun x=> ∑ j∈q,F j x) from funext (r.decomposition M T D i h f w p)]
   apply (Dust.finite q (fun x hx=> (hv x f w p c hp h₁))).mono; have he:0 ≤ c:= h₁.pos; have hB':0< b:= r.bag_pos w d (hB w); have hd:0<D':= Finset.prod_pos (f:=fun x=>kick f x γ) (fun j _=>kick_pos j f); change ∑ j∈ q,t j*c*b*D'≤C*c*b*D'; simp_rw [← Finset.sum_mul]; gcongr; exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ q) (fun i _ _=> (ht i).le)

omit [BorelSpace E] [Fintype I] [CompleteSpace X] [(volume:Measure E).IsAddHaarMeasure] h in
lemma given_drops {u : Type} (f : u→W)(hp : Given T) : Given (T ∘ f):= ⟨hp.choose,fun i j=>hp.choose_spec i (f j)⟩
omit h
lemma achieved (A : Services C F S) (h : Loan Z M r B D) (hm : r.Authority M d) (hp : Given T)(hR : Economy Q γ): ∃ C >(0:ℝ), Achieves Z M r T B D γ C := by
    -- induction on number of remaining possible splits
    suffices he: ∀ n:ℕ, g.card-Q.parts.card=n → ∃ C>(0:ℝ), Achieves Z M r T B D γ C from he _ rfl
    intro n H; induction n using Nat.strong_induction_on generalizing W I Q with
    | h n ih=>
      by_cases hY : ∀ i∈ Q.parts,i.card ≤ 1; exact r.achieved_alone hY M T D h hp hR
      push Not at hY; obtain ⟨i,hi,hI⟩:=hY; let j : Q.parts:=⟨i,hi⟩; have hs : 1 < j.val.card:=hI
      let u:Fans P j.val:= Classical.choice (available_fans P (r.displaysNormals i hi) (Q.nonempty_of_mem_parts hi)); have hB(w):0<B w:= h.currency.pos _ (Set.mem_univ _)
      apply r.all_armed M T D j hs hB hR; intro b
      obtain ⟨C,hC,h⟩:= r.cost_one M T D j b u hs hB hR (fun v=> by
            let a:= r.renew j (outward b) u v hs; let q:= replace j v.val; have hc:n> g.card-q.parts.card:=by have hh:=(replace_finer j v.property); have he:q.parts.card≤g.card:=q.card_parts_le_card; change n>g.card-(replace j v.val).parts.card; change (replace j v.val).parts.card≤g.card at he; omega -- omega
            exact ih _ hc _ _ _ (r.loan_listens j u v b A h hs hm) ( (show a.Authority M d from hm)) (given_drops T _ hp) (hR.inherited j v) rfl)
      exact r.pass M T D j b hs C hC hR h hB
end YM.Contacts.Harvest.Route
