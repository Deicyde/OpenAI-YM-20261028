import YM.UVExtension.Copse.Scent
import YM.UVExtension.Yard.Coat
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Reseve
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Copse
open Function Filter Set RG Wilson Lattice Precision Push Push.AbsoluteSums Animals Finset Progress.DirectedRecipe Payments
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Mallow Extra.Iteration MeasureTheory
open Lamppost Concert Ovens Ovens.Pipes
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {D Z:Type}{G:Gauge}{n:Side} {X:Pipes G n} [NormedAddCommGroup Z][NormedSpace ℂ Z]{T:Opening D Z}
variable (S:ℕ≃ X.Pellet)(q:BudgetPoint)
variable {p:BudgetPoint} (Y:D→ Ovens.Tap G n){b c g h r k:ℝ}(H:Atlas (bell X.kernel p.B (p.supportExponent+1)) T (fun i j u=> (Y i).forced j u) (fun _=>b))(J:Atlas (softer X p.B (p.supportExponent+1)) T (fun i j u=> (Y i).logarithm j u) (fun _=>c))
set_option quotPrecheck false
abbrev downs (X:Ovens.Pipes G n) (p:BudgetPoint) (d:ℕ):= Copse.nose (G:=G) (fun i=>(X.kernel i).support) d p.B (p.supportExponent+1)
variable (F:D→ℝ→Ovens.Code G n) (d:ℕ) (M:Scent (downs X p d) T F (fun _=>g)) (hF:∀ i,F i 0=(Y i).forced)
local notation "V0"=> rind Y H J
noncomputable def pet (z:Z)(i:ℕ)(u:Config G n):ℂ:= if (addr S q i).eligible q.threshold u then ∑ j ∈ (S i).val,(∏ k∈ (S i).val.erase j, rind Y H J u k z) * Sum.elim (fun i=> M.f z i u) (fun _=> 0) j else 0
noncomputable def salt (i:D)(x:ℕ)(u: Config G n) := if (addr S q x).eligible q.threshold u then ∑ j∈(S x).val, (∏ k∈(S x).val.erase j,Pipes.reach (Y i) k u)*j.elim (fun j=> breezeM (downs X p d) F i j u) (fun _=>0) else 0
include H J M hF
omit H J in
lemma portalS (i:D)(u:Config G n)(j:ℕ): HasDerivAt (fun z=> solid S q (spice (Y i) (F i z)) j u) (salt (p:=p) S q Y F d i j u) 0:=by
   unfold salt solid; split; swap; · exact hasDerivAt_const _ _
   let f x theta:= Pipes.reach (spice (Y i) (F i theta)) x u; have hg x:f x 0=Pipes.reach (Y i) x u:=by unfold f; rw [hF]; rfl
   let f' (x:Ovens.Label):= x.elim (fun j=> breezeM (downs X p d) F i j u) (fun _=>0); have hx (x:Ovens.Label): HasDerivAt (f x) (f' x) 0 := by cases x with
                                                                                                                        | inl j=> exact flair (downs X p d) M i j u
                                                                                                                        | inr z=> exact hasDerivAt_const (0:ℝ) (Pipes.reach (Y i) (.inr z) u)
   have ht:= HasDerivAt.fun_finsetProd (u:=(S j).val) (fun i _=> hx i); simp_rw [hg,smul_eq_mul] at ht; exact ht

omit hF
lemma petals (z:D)(i:ℕ)(u:Config G n): pet S q Y H J F d M (T.call z) i u= ↑(salt (p:=p) S q Y F d z i u):=by
   unfold pet salt; split; swap; · exact Complex.ofReal_zero.symm
   rw [Complex.ofReal_sum]; apply Finset.sum_congr rfl; intro j _; push_cast; refine congr_arg₂ (·*·) (Finset.prod_congr rfl (fun k _=> ?_)) ?_
   · rcases k with i|i; exact H.exacts ..
     change Complex.exp _-_=↑(Real.exp _-1:ℝ)
     push_cast; rw [J.exacts]
   cases j; · exact M.exacts ..
   exact Complex.ofReal_zero.symm
lemma pen (i:ℕ)(u : Config G n): Bumps T.span (fun z=> pet S q Y H J F d M z i u):=by
   intro U f h hp hg; unfold pet; split; swap; · exact differentiableOn_const _
   refine DifferentiableOn.fun_sum (fun i _=>?_); refine DifferentiableOn.mul (DifferentiableOn.fun_finsetProd (fun i _=>?_)) ?_
   · rcases i with i|i; · exact H.pulse i u U f h hp hg
     exact ((J.pulse i u U f h hp hg).cexp).sub_const _
   cases i with
   | inl i=> exact M.pulse i u U f h hp hg
   | inr i=> exact differentiableOn_const _
-- cost.K: at each occurrence linear map. signed.S measure.
variable (P:Payments.Rates p.B h b c k)
include P
lemma gauges (z:Z)(hz:z∈T.span):
    Meter.MeasureP (nose (G:=G) (fun i=> (addr S q i).support) d p.B p.supportExponent) (fun i u=> pet S q Y H J F d M z i u) g := by
    obtain ⟨f,hf,hA⟩:= (H.bounds z hz).afloat; obtain ⟨b₀,hg,hB⟩:= (J.bounds z hz).afloat; obtain ⟨u,hu,hM⟩:= (rests d p.B).mp (M.bounds z hz)
    let A i:= Real.exp k*f i; let W:= inflation b c k; let Q:= Sum.elim A (fun i=> 2*b₀ i); let f': ℕ ⊕ ℕ → ℝ:=Sum.elim u (fun i=>0)
    have hx :Ac.Hit X.patch p.B Q (p.supportExponent+1) W:=fun i=> Cost.sum (AnalyticBridge.VerifiedReset.Quotes.hit_scale (Real.exp_pos k).le ((bellbook ..).1 hA) i) (AnalyticBridge.VerifiedReset.Quotes.hit_scale zero_le_two ((soot X _ _ _ _).1 hB) i)
    have hG(i): b₀ i ≤1:= by
       obtain ⟨x,hx⟩:= X.sites i; have he := budget_single (hB x) i
       simp only [Concert.softer,if_pos hx] at he; exact (le_mul_of_one_le_left (hg i).1 (Real.one_le_exp (mul_nonneg (add_nonneg p.exponent_pos.le zero_le_one) (Nat.cast_nonneg _)))).trans (he.trans P.soft_limit)
    have hZ i:0≤ Q i:= by rcases i with i|i; exact mul_nonneg (Real.exp_pos _).le (hf i).1; exact mul_nonneg zero_le_two (hg i).1
    have ha(i:Ovens.Label)(V:Config G n): ‖rind Y H J V i z‖ ≤ Q i:=by
       rcases i with i|i; · exact ((hf i).2 V).trans (le_mul_of_one_le_left (hf i).1 (Real.one_le_exp P.heading))
       exact (Complex.norm_exp_sub_one_le (((hg i).2 V).trans (hG i))).trans (mul_le_mul_of_nonneg_left ((hg i).2 V) zero_le_two)
    have hp(i):0≤f' i:= by rcases i with i|i; exact (norm_nonneg _).trans (hM i 1); exact le_rfl
    have hU:SumBudget (fun i=> f' i*worth d p.B (p.supportExponent+1) (X.patch i)) g:=by nth_rw 1 [← add_zero g]; exact Cost.sum hu (show SumBudget (fun i:ℕ=> (0:ℝ)*worth d p.B (p.supportExponent+1) (X.patch (.inr i))) 0 from (by simp [SumBudget]))
    let g (i) (j):= (∏ k∈(S i).val.erase j,Q k)*f' j; let t(i):=∑ j∈(S i).val,g i j; have ht(i j):0≤g i j:=mul_nonneg (Finset.prod_nonneg fun j _=> hZ j) (hp _); let P':= compass X.patch p.B d hZ hx (show (ballCost p.B:ℝ)*W ≤ 1 from (by unfold ballCost; push_cast; convert! P.capital using 1; push_cast; ring)) (budget_nonneg (hx 0)) p.exponent_pos.le f' _ hp hU
    apply (rests d p.B).2; refine ⟨t, ?_,fun i U=>?_⟩; swap
    · unfold pet; split; swap; · exact norm_zero.trans_le (Finset.sum_nonneg fun _ _=> ht i _)
      refine (norm_sum_le ..).trans (Finset.sum_le_sum (fun j hj=>?_)); rw [norm_mul,norm_prod]; refine mul_le_mul (Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun k _=> ha k _)) ?_ (norm_nonneg _) (prod_nonneg fun j _=> hZ j); rcases j with j|j; exact hM _ _; exact norm_zero.le
    let e:= Subtype.val ∘ S; have h:= budget_pull e (Subtype.val_injective.comp S.injective) P'; refine budget_mono h (fun i=>mul_nonneg (Finset.sum_nonneg fun j _=>ht _ _) (Real.exp_pos _).le) fun i=>?_ ; unfold t; rw [sum_mul]
    change _ ≤ ∑ j∈(S i).val,f' j*flight X.patch p.B d Q j p.supportExponent (S i).val; refine Finset.sum_le_sum fun j hj=>?_; unfold flight; rw [if_pos ⟨hj,(S i).property.2.1⟩]; change g i j*worth d p.B p.supportExponent (X.skin (S i).val)≤ _; unfold g skin; apply le_of_eq; ring

-- package
include hF
lemma petalsT : Nonempty (Scent (nose (G:=G) (fun i=> (addr S q i).support) d p.B p.supportExponent) T (fun i z=> solid S q (spice (Y i) (F i z))) (fun _=>g)):=by
    refine ⟨⟨⟨pet S q Y H J F d M,fun i j u=>?_,fun i u=> pen S q Y H J F d M i u, fun i hi=> gauges S q Y H J F d M P i hi⟩,fun i j u=> (portalS S q Y F d M hF i u j).differentiableAt⟩⟩
    exact (petals S q Y H J F d M _ _ _).trans (congr_arg Complex.ofReal (portalS S q Y F d M hF i u j|>.deriv.symm))
end YM.UVExtension.Copse
