import YM.MergeProof.North.Broom
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι:Type}{G:Gauge}{n c:Side}{R:Rep G n}{Q:Rep G c}{S:StepData c n}{D:GaugeDoor R Q}{x y z a b t A:ℝ}{p:ℂ} {o:Site n}{g:Config G n→ℂ}{P: Res G n}{K: ℕ→ Config G n→ℂ}
lemma push_list (F:ι→ Config G n→ℂ)(h:∀ i,Integrable (F i) (prior G n))(s: Finset ι)(he:S.IsKernel x G): S.push x (∑ i∈s,F i)=∑ i∈s,S.push x (F i):=by induction s using Finset.induction_on with
    | empty=> funext i; simp [StepData.push]
    | @insert i s hi IH=> rw [Finset.sum_insert hi,Finset.sum_insert hi,StepData.push_add he _ _ (h i) ?_,IH]; exact integrable_finsetSum' _ (fun i _=>h i)
lemma spill_in (h:Blade R o g (profile R.activities K) p t)(hr:R.Lawful x y z a b)(hq:Dominated K): Integrable (coin R g K) (prior G n):=by
   obtain ⟨I,i,M,s,h⟩:=h; rw [h.display hr.labels hq]; have hy(i:Leaf R): Integrable (Complex.ofReal ∘ i.cicada) (prior G n):= ((i.sells hr).1.integrable _).ofReal
   exact ((((R.envelope hr).integrable _).ofReal).smul _).add (integrable_finsetSum' _ (fun j _=> (hy _).smul _))
def Runs (D:GaugeDoor R Q)(S:StepData c n)(A:ℝ): Prop:= ∀ (M:Leaf R)(o:Site n),o∈ M.crest → let f:= fun i=>Complex.ofReal ∘ D.hinge M i; Dominated f ∧ ∃ g:Config G c→ℂ,Blade Q (S.ratio.parent o) g (profile Q.activities f) 0 (A* MergeProof.load M)∧ S.push R.beta (Complex.ofReal ∘ M.cicada)= coin Q g f
lemma slosh (h:Blade R o g (profile R.activities K) p t)(hr:R.Lawful x y z a b)(hq:Dominated K)(hx:Runs D S A)(hd:0≤A){a' b' : ℝ}
    (hu: Q.activities.Valid Q.p a' b') (hf:S.push R.beta R.eval= Q.eval) (hp:S.IsKernel R.beta G): ∃ (f:Config G c→ℂ)(k:ℕ → Config G c→ℂ), Blade Q (S.ratio.parent o) f (profile Q.activities k) p (A*t) ∧ Dominated k∧ (∃ s:Set Wing,s.Finite∧ Tale s o (S.ratio.parent o) 1 g (profile R.activities K) (profile Q.activities k) p t 0 D) ∧ S.push R.beta (coin R g K)=coin Q f k:=by
    obtain ⟨I,i,M,s,h⟩:= h; let f i j:=Complex.ofReal ∘ D.hinge (M i) j
    choose H F hF hB using fun i=> (hx _ _ (h.sit i))
    let X i:=s i • f i; have hk i:Dominated (X i):=rainbow (H i) _; let K':=∑ i,X i; have hK:Dominated K':=combies X hk univ
    have ht:profile Q.activities K'= ∑ i,s i • quoted D (M i):=by unfold K'; rw [prof_sum X hk];exact Finset.sum_congr rfl fun i _=> profile_scale ..
    let y':= (fun _:Config G c=> p); let P':=∑ i,s i • F i
    refine ⟨y'+P',K',?_ ,hK,⟨_,Set.finite_range _, h.to_tale (S.ratio.parent o) _ ht⟩,?_⟩
    · have hv:= ((blade₀ (R:=Q) (o:=S.ratio.parent o) (u:=p) (a:=0) le_rfl).comp (comp_many _ _ _ _ Finset.univ (fun i _=> (hF i).rate (s i))))
      simp only [zero_add,mul_zero,Finset.sum_const_zero,add_zero] at hv; rw [ht]
      apply hv.more; rw [← show ∑ i, A*(‖s i‖*load (M i))= ∑ i, ‖s i‖*(A* load (M i)) from Finset.sum_congr rfl fun i _=>mul_left_comm ..]; rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h.pay hd
    rw [h.display hr.labels hq]; have hy(i:Leaf R): Integrable (Complex.ofReal ∘ i.cicada) (prior G n):= ((i.sells hr).1.integrable _).ofReal
    have he : Integrable (Complex.ofReal ∘ R.eval) (prior G n):= ((R.envelope hr).integrable _).ofReal
    rw [StepData.push_add hp _ _ (he.smul p) (integrable_finsetSum' _ (fun i _=> (hy (M i)).smul (s i))),StepData.push_smul _ _ _ _ he,flash,hf,push_list _ (fun i=> (hy (M i)).smul (s i)) _ hp]
    simp_rw [show ∀ i,S.push R.beta (s i • (Complex.ofReal ∘ (M i).cicada))= s i • coin Q (F i) (f i) from fun i=> ((StepData.push_smul _ _ _ _ (hy _)).trans (congr_arg _ (hB i)))] -- indentation
    rw [show K'=0+∑ i,X i by rw [zero_add],coin_plus Q _ _ pawn0 hK hu.boundK]; unfold P'; rw [coin_sum X _ hk _ hu.boundK]; simp_rw [X,coin_mul]
    congr 1; funext U; rw [coin₀]; exact mul_comm ..
end YM.MergeProof.Float
