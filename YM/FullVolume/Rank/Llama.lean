import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Blush.Wind
import YM.FullVolume.Mark.Hinge
import YM.FullVolume.Umbra.Liner
/-! continuity in the actual dictionary, incl marker forced charges. Families ℂ. Shape annotations per true support, with threshold comparisons incl equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Paint
open Function Filter Set MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
open MergeProof MergeProof.Matric ConnectedActivityE6 Lim Neptune
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{n:Side}{S:Desk G n}{A:Hol G}{P:BudgetPoint}{ι κ:Type}{E:Type}[NormedAddCommGroup E]
-- conjugations in metric component. angels reserved.
structure Bill (f:ℕ→ι→ Config G n→ℂ):Prop where
   use: ∃ v:ℕ→ι→ℝ,Sparse v∧∀ n i V,‖f n i V‖ ≤ v n i
structure Credit (f g:ℕ→ι→ Config G n→ℂ):Prop where
   left: Bill f
   right: Bill g
   polls: ∀ i (V:ℕ→ Config G n), Tendsto (fun j=> f j i (V j)-g j i (V j)) atTop (𝓝 0)
-- from point numbers.C
namespace Credit
variable {f g z y:ℕ→ι→ Config G n→ℂ}
lemma castC {f g:ℕ→ι→ Config G n→ℝ}(h:Angel f g):Credit (fun n i U=>(f n i U:ℂ)) (fun n i U=>(g n i U:ℂ)):=by
    obtain ⟨u,hu,U⟩:=h.a.sup; obtain ⟨v,hv,V⟩:=h.b.sup
    refine ⟨⟨_,hu,fun n i x=> (Complex.norm_real ..).trans_le (U ..)⟩,⟨_,hv,fun n i x=> (Complex.norm_real ..).trans_le (V ..)⟩, fun i z=>?_⟩; have h':= Complex.continuous_ofReal.continuousAt.tendsto.comp (h.star i z); simpa only [Complex.ofReal_zero,Function.comp_def,Complex.ofReal_sub] using h'
lemma scal (h:Credit f g)(a:ℂ): Credit (fun n i=> a • f n i) (fun n i=> a • g n i):=by
    obtain ⟨u,hu,U⟩:= h.left.use; obtain ⟨v,hv,V⟩:= h.right.use; refine ⟨⟨_,hu.climb (norm_nonneg a),fun n i x=>?_⟩,⟨_,hv.climb (norm_nonneg a),fun n i x=>?_⟩,fun i z=>?_⟩
    · rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (U ..) (norm_nonneg _)
    · rw [Pi.smul_apply,norm_smul]; exact mul_le_mul_of_nonneg_left (V ..) (norm_nonneg _)
    simp_rw [Pi.smul_apply,← smul_sub]; simpa only [smul_zero] using (h.polls i z).const_smul a
lemma sum (h:Credit f g)(he:Credit y z): Credit (fun n=> f n+y n) (fun n=>g n+z n) :=by
    obtain ⟨u,hu,U⟩:=h.left.use; obtain ⟨v,hv,V⟩:=h.right.use; obtain ⟨x,hx,hX⟩:=he.left.use; obtain ⟨w,hw,W⟩:=he.right.use; refine ⟨⟨_,hu.tug hx,fun n i v=>(norm_add_le ..).trans (add_le_add (U ..) (hX ..))⟩,⟨_,hv.tug hw,fun n i v=>(norm_add_le ..).trans (add_le_add (V ..) (W ..))⟩,fun i v=>?_⟩
    simp_rw [Pi.add_apply, add_sub_add_comm]; exact (add_zero (0:ℂ)) ▸ ((h.polls i v).add (he.polls i v))
lemma buys (h:Credit f g) (i:ι) (a:ℝ)(ha:0<a):∀ᶠ j in atTop,∀ V,‖f j i V-g j i V‖ ≤ a:=by
    by_contra hh; choose! p hp using fun n (hn:¬∀ V,‖f n i V-g n i V‖≤a)=> Classical.not_forall.mp hn; exact hh (((h.polls i p).norm.eventually (ge_mem_nhds (by simpa using ha : ‖(0:ℂ)‖<a))).mono fun n he=> Classical.byContradiction fun h=> hp n h he)
end Credit
structure SumE (f:ℕ→ι→ Config G n→ℂ)(P:BudgetPoint)(A:ι→Support n):Prop where
    reg:∀ n i,P.Regular (A i) (f n i)
    pay: ∃ v:ℕ→ι→ℝ,Sparse v∧∀ n i,P.supBounds 0 (A i) (f n i) (v n i)
structure SeatE (f g : ℕ→ι→ Config G n→ℂ)(P:BudgetPoint)(A:ι→Support n) :Prop where
    vista:SumE f P A
    vests:SumE g P A
    cost i ε: 0<ε →∀ᶠ j in atTop,P.supBounds 0 (A i) (f j i-g j i) ε
namespace SeatE
variable {f g z y:ℕ→ι→ Config G n→ℂ}{s:ι→Support n}
lemma scaler (h:SeatE f g P s)(a:ℂ): SeatE (fun n i=> a • f n i) (fun n i=> a • g n i) P s:=by
   obtain ⟨v,hv,hV⟩:= h.vista.pay; obtain ⟨q,hq,hQ⟩:= h.vests.pay
   refine ⟨⟨fun n i=>regular_smul _ (h.vista.reg ..),_,hv.climb (norm_nonneg a), fun n i=> bound_smul _ (hV ..)⟩,⟨fun n i=> regular_smul _ (h.vests.reg ..),_,hq.climb (norm_nonneg a),fun n i=> bound_smul _ (hQ ..)⟩,fun i ε hp=>?_⟩
   by_cases he:a=0; subst a; simp_rw [zero_smul,sub_zero]; exact Eventually.of_forall fun n=> bound_weaken ((regular0 ..).2) hp.le
   have hh:= norm_pos_iff.mpr he; filter_upwards [h.cost i _ (div_pos hp hh)] with j hj; rw [← smul_sub]; exact bound_weaken (bound_smul _ hj) (by field_simp; norm_num)
lemma sum (h:SeatE f g P s)(he:SeatE y z P s): SeatE (fun n=> f n+y n) (fun n=>g n+z n) P s:=by
   have hh {g g':ℕ→ι→ Config G n→ℂ}(h:SumE g P s)(hp:SumE g' P s):SumE (fun n=>g n+g' n) P s:=by
      obtain ⟨v,hv,hV⟩:= h.pay;obtain ⟨q,hq,Q⟩:=hp.pay; exact ⟨fun i k=> Next.Foundations.regular_add (h.reg ..) (hp.reg ..),_,hv.tug hq, fun i k=> Next.Foundations.bound_add (h.reg ..) (hp.reg ..) (hV ..) (Q ..)⟩
   refine ⟨hh h.vista he.vista,hh h.vests he.vests,fun i ε hq=>?_⟩
   filter_upwards [h.cost i _ (half_pos hq), he.cost i _ (half_pos hq)] with j hj hx; rw [Pi.add_apply,Pi.add_apply,add_sub_add_comm]; exact bound_weaken (Next.Foundations.bound_add (regular_sub (h.vista.reg ..) (h.vests.reg ..)) (regular_sub (he.vista.reg ..) (he.vests.reg ..)) hj hx) (add_halves ε).le
lemma castC {F G':ℕ→ι→ Config G n→ℝ}{Z:ι→RegularAddress n}(h:Canopy P Z F G')(he:∀ i, (Z i).support=s i)(hz:∀ i,(Z i).site=0): SeatE (fun n i=> Complex.ofReal ∘ F n i) (fun n i=> Complex.ofReal ∘ G' n i) P s:=by
    have H(P':ℕ→ι→ Config G n→ℝ)(h:PulseWise P Z P'):SumE (fun n i=> Complex.ofReal ∘ P' n i) P s:=by
       obtain ⟨v,hv,hV⟩:=h.sup; refine ⟨fun n i=> he i ▸ Blush.ornate (h.chart ..),_,hv,fun n i=> ?_⟩
       have hh:= Blush.pricingG (h.chart n i) (hV n i); rw [hz i,he i] at hh; exact hh
    refine ⟨H _ h.a,H _ h.b,fun i b hx=>?_⟩; filter_upwards [h.sails i b hx] with j hj; have hf:= Blush.pricingG (AnalyticBridge.VerifiedReset.reg_sub (h.a.chart j i) (h.b.chart j i)) hj
    rw [hz i,he i] at hf; have hp: Complex.ofReal ∘ (F j i-G' j i)= Complex.ofReal ∘ F j i-Complex.ofReal ∘ G' j i:= funext fun _=>Complex.ofReal_sub _ _; rw [hp] at hf; exact hf
lemma extendsE (b:κ→Support n)(h: SeatE f g P s)(i:ι↪κ)(hs:∀ p,b (i p)=s p): SeatE (fun n=>Progress.DirectedRecipe.stuff i (f n)) (fun n=>Progress.DirectedRecipe.stuff i (g n)) P b:=by
    have hp (f:ℕ→ι→ Config G n→ℂ)(h:SumE f P s):SumE (fun n=> Progress.DirectedRecipe.stuff i (f n)) P b:=by
       obtain ⟨v,hv,hV⟩:=h.pay; refine ⟨fun n j=>?_,_, Ledgers.hopper hv i,fun n j=>?_⟩
       · by_cases hj:j∈ Set.range i; obtain ⟨k,rfl⟩:= hj; rw [Progress.DirectedRecipe.stuffed,hs]; exact h.reg ..; rw [Progress.DirectedRecipe.blank _ _ hj]; exact (regular0 _ _ 0).1
       by_cases hj:j∈ Set.range i; obtain ⟨k,rfl⟩:=hj; rw [Progress.DirectedRecipe.stuffed,Progress.DirectedRecipe.stuffed,hs]; exact hV ..; rw [Progress.DirectedRecipe.blank _ _ hj,Progress.DirectedRecipe.blank _ _ hj]; exact (regular0 ..).2
    refine ⟨hp _ h.vista,hp _ h.vests,fun j ε hε=> ?_⟩
    by_cases he:j∈ Set.range i; obtain ⟨k,rfl⟩:=he; rw [hs];simp_rw [Progress.DirectedRecipe.stuffed]; exact h.cost k ε hε
    exact Eventually.of_forall fun n=> by rw [Progress.DirectedRecipe.blank _ _ he,Progress.DirectedRecipe.blank _ _ he,sub_zero]; exact bound_weaken ((regular0 ..).2) hε.le
end SeatE
end YM.FullVolume.Paint
