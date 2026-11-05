import YM.MergeProof.North.Jazz
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι:Type}{G:Gauge}{n c:Side}{R:Rep G n}{κ e t z a:ℝ} {o:Site n}{P:BudgetPoint}{S:Support n}{f:Config G n→ℝ}
lemma assets (h:P.Regular S f) : UsesFinal P.threshold S (masked P.threshold S f) ∧ GaugeInvariant (masked P.threshold S f):=by
   constructor
   · intro U V hp he; have hh: Healthy P.threshold S U ↔ Healthy P.threshold S V:= by unfold Healthy; rw [disjoint_iff_inter_eq_empty,disjoint_iff_inter_eq_empty,he]
     unfold masked; simp only [Set.indicator,Set.mem_setOf_eq,hh,h.sites U V hp]; rfl
   intro i U; unfold masked Healthy; simp only [Set.indicator,Set.mem_setOf_eq,gauge_flags,h.symmetry i U]; split_ifs<;> rfl
lemma jacking [Countable ι] (A:Menu.Arsenal R)(F:ι→ Config G n→ℝ)(X:ι→Support n)(h:∀ i,R.p.Regular (X i) (F i))(hp:∀ i,o∈X i){g:ι→ℝ}(hh:∀ i U,‖masked R.p.threshold (X i) (F i) U‖≤ g i)(he:SumBudget (fun i=>R.p.mass (X i) (g i)) t) : Blade R o (fun U=> ∑' i,Complex.ofReal (masked R.p.threshold (X i) (F i) U)) 0 0 (2*t):=by
   apply carriage A (fun i U=> Complex.ofReal (masked R.p.threshold _ (F i) U)) X (fun i g U=> congr_arg Complex.ofReal ((assets (h i)).2 g U)) (fun i=> Complex.continuous_ofReal.measurable.comp (masked_measurable _ _ _ (h i).borel)) hp (fun i U V h₁ h₂=> congr_arg Complex.ofReal ((assets (h i)).1 U V h₁ h₂)) (fun i U h=> Classical.byContradiction (fun hn=>h (by simp [hn]))) (fun i U=> (Complex.norm_real _).trans_le (hh i U)) he
-- Envelope real lifting PUSH
lemma flash (S:StepData c n) (R:Rep G n) (f:Config G n→ℝ) : S.push R.beta (Complex.ofReal ∘ f)=Complex.ofReal ∘ S.push R.beta f:=by
   funext i
   unfold StepData.push; simp_rw [Function.comp_apply,Complex.real_smul,smul_eq_mul,← Complex.ofReal_mul, integral_complex_ofReal]
end YM.MergeProof.Float
