import YM.TraceExtension.Shepherd.Poise
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Shepherd
open RG Wilson Lattice Source AnalyticBridge VerifiedReset Finset Ac MergeProof Cask Function Pressure Next.Fluctuations PathData Extra.Iteration Push.AbsoluteSums Extra.Multi StressFlux MeasureTheory
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical ContDiff
variable {G:Gauge}{n:Side} (R:Rep G n)(x:Site n)(d:Step) {σ A v δ u:ℝ}(h:R.Lawful σ A v δ u)(H:Geo.Width R.p R.clip σ)(hv:WilsonStartup.Decent R.clip R.p)(he:4 ≤ R.p.supportExponent) (m:ℕ)
local notation "W!"=> R.path
local notation "b!"=> R.p.threshold
local notation "M!"=> R.p.B
local notation "d!"=> R.p.supportExponent
local notation "X"=> Config G n
variable (J:Config G n→ G.El →ℂ)(ν:G.El→ G.El){P:Support n}{D:ℝ}
variable (w: ProofC R x J ν P D)
local notation "t!"=> EBook R x m
abbrev widthP (p:Finset (EBook R x m))(D:Support n):=D∪p.biUnion Subtype.val
include w
lemma actME : Measurable (uncurry (stunt x d ν)) := by
   apply measurable_pi_lambda; intro i
   unfold uncurry; unfold stunt StressFlux.modify; split_ifs
   all_goals (first| exact ((Measurable.comp (measurable_pi_apply i) measurable_fst).mul ((w.borel.comp measurable_snd).inv)) | exact ((w.borel.comp measurable_snd).mul (Measurable.comp (measurable_pi_apply i) measurable_fst))| exact ((measurable_pi_apply i).comp measurable_fst))
lemma ruleP : Envelope (uncurry (spur x d J ν)):= based w.env (fun k:X × G.El=> (stunt x d ν k.1 k.2,k.2)) (show Measurable _ from Measurable.prodMk (actME R _ d _ ν w) measurable_snd)
lemma siteP (j:G.El) : LocalOn P (fun U:X=>spur x d J ν U j):=fun U V hu=> w.eye j _ _ (modify_local x d _ P hu)
lemma gazeP (U:X)(V: Site n→G.El)(j:G.El): stunt x d ν (Lattice.gauge V U) (V x*j)= Lattice.gauge V (stunt x d ν U j):= by rw [stunt,stunt,w.turns,modify_g]
lemma diary (U:X)(V: Site n→ G.El)(j:G.El): spur x d J ν (Lattice.gauge V U) (V x*j)=spur x d J ν U j:=by unfold spur; rw [gazeP R x d J ν w U V j,w.gear]
include h H hv he
lemma works (p:Finset (EBook R x m)) : Envelope (uncurry (braid R x d m J ν p)) ∧ (∀ U:X,∀ (V:Site n→G.El)(j:G.El), braid R x d m J ν p (Lattice.gauge V U) (V x*j) = braid R x d m J ν p U j) ∧
    ∀ j,UsesFinal b! (widthP R x m p P) (fun U=> braid R x d m J ν p U j):=by
   let f:= trio R x d m J ν; let e:=spur x d J ν; let S:= widthP R x m p P
   have hS(i : t!) : Envelope (uncurry (f i)):=by
       let g:= stockC R i.val; have hq:= floated R h H hv he i.val; have hm : Envelope (fun k:X×G.El=> g (stunt x d ν k.1 k.2)):= by obtain ⟨c,H⟩:=hq.cost; exact ⟨hq.meas.comp (actME R _ d _ ν w), c,fun v=>H _⟩
       have hv' :Envelope (fun k:X×G.El=> g k.1):=by obtain ⟨c,H⟩:=hq.cost; exact ⟨hq.meas.comp measurable_fst, c,fun v=> H _⟩
       let q(k:X × G.El):= g (stunt x d ν k.1 k.2)-g k.1; have hc:Envelope q:= by unfold q; simp_rw [sub_eq_add_neg]; exact hm.add hv'.neg
       have hz:Envelope (fun k:X×G.El=>Real.exp (q k)-1):=by simp_rw [sub_eq_add_neg]; exact hc.exp.add (Envelope.const _)
       have ht: Envelope (fun k:X×G.El=> if e k.1 k.2=0 then 0 else Real.exp (q k)-1):= Envelope.piece ((ruleP R x d J ν w).meas (measurableSet_eq (a:= (0:ℂ)))) (Envelope.const _) hz
       have HH:uncurry (f i)=Complex.ofReal ∘ (fun k:X × G.El=> if e k.1 k.2=0 then 0 else Real.exp (q k)-1):=funext fun k=>by change trio R x d m J ν _ _ _ = Complex.ofReal _; unfold trio e; split <;> simp [*,q,g]
       rw [HH]; exact fromR ht
   refine ⟨envUmul (ruleP R x d J ν w) (envUprod p (fun i=>uncurry (f i)) (fun i _=> hS i)), fun U V j=>?_,fun j U V hu hh=> ?_⟩
   · unfold braid; rw [diary R _ d J ν w]; apply congr_arg (_ * ·) (Finset.prod_congr rfl ?_); intro i hi; unfold trio; rw [diary R x d J ν w, gazeP R _ d J ν w, (stock_pay R h i.val hv).2.1,(stock_pay R h i.val hv).2.1]
   have hy : spur x d J ν U j=spur x d J ν V j:= siteP R _ d _ _ w j U V (agrees_mono hu (coe_subset.mpr subset_union_left))
   change braid R x d m J ν p U j = braid R x d m J ν p V j; by_cases hx: spur x d J ν U j=0; unfold braid; rw [← hy,hx];ring
   have hG := (actsD R x d h H hv he J ν w U j hx).1; have hU := (actsD R x d h H hv he J ν w V j (hy ▸ hx)).1
   unfold braid; rw[hy]; apply congr_arg (_ * ·) (Finset.prod_congr rfl ?_); intro i hi
   have hs:i.val⊆S:= Finset.Subset.trans (Finset.subset_biUnion_of_mem _ hi) Finset.subset_union_right
   have hm : i.val∩flags b! U=i.val∩flags b! V:=by conv_lhs=> rw[← inter_eq_left.mpr hs,inter_assoc, (show S∩_=S∩_ from hh), ←inter_assoc,inter_eq_left.mpr hs]
   have hZ:Agrees i.val U V:=agrees_mono hu (coe_subset.mpr hs)
   have ht:= (stock_pay R h i.val hv).2.2; unfold trio; rw [hy,ht U V hZ hm,ht (stunt x d ν U j) (stunt x d ν V j) (modify_local x d _ i.val hZ) (by rw[hG,hU,hm])]
-- priced sum, not counting number of (zero-weight) events.Hit exact exp*α
lemma earns (xP:x∈P)(e p:ℝ) (he':0≤ e)(ht:e ≤ d!-1) (ha: ∀ U k, ‖J U k‖ ≤ p)(hp:0 ≤ p)(v':Support n→ℝ)(hk:∀ i, 0 ≤ v' i ∧ ∀ U V : Config G n, Brink R D U V → |stockC R i U-stockC R i V| ≤ v' i)
    (a:ℝ)(hx:Hit id M! v' (d!-1) a)(hv':a≤1):∃ c:Finset (EBook R x m)→ℝ,(∀ i,0 ≤ c i ∧∀ U k, ‖braid R x d m J ν i U k‖ ≤ c i)∧
        ∑ j, c j*Real.exp (e*coverNumber M! (widthP R x m j P)) ≤ p*Real.exp (e*coverNumber M! P)*Real.exp 2:=by
   let f(i:EBook R x m):=2*v' i.val; have hh(i:t!):0 ≤ f i:= mul_nonneg zero_le_two ((hk i.val).1); let c(p:Finset (EBook R x m)):= ∏ i∈p,f i
   have hT(i : Finset (EBook R x m)): coverNumber M! (widthP R x m i P) ≤ coverNumber M! P+∑ j∈i,coverNumber M! j.val:=by
        induction i using Finset.induction_on with
        | empty=>simp[widthP]
        | insert i s hi IH=>
            let V:= widthP R x m s P; rw [show widthP R x m (insert i s) P= i.val ∪ V from (by unfold V widthP; rw [biUnion_insert,union_left_comm]),sum_insert hi, add_left_comm]; exact (Corona.meets_sum i.property.1 (show x∈V from mem_union_left _ xP) M!).trans (Nat.add_le_add_left IH _)
   let g (i:t!):= f i*Real.exp (e*coverNumber M! i.val)
   have hy : ∑ i,g i≤ 2:=by
       let v (i:t!):=v' i.val*Real.exp ((d!-1)*coverNumber M! i.val); have hz : ∑ i,v i ≤ a:=by
           refine le_trans ?_ (Extra.Multi.Budget.cap (hx x) (univ.image (Subtype.val (p:=SBook R x m))))
           rw [sum_image Subtype.val_injective.injOn]; refine sum_le_sum fun i _=> ?_; rw [if_pos (show x∈id i.val from i.property.1)]; exact le_rfl
       have hp : ∑ i,g i ≤ ∑ i, 2*v i:=sum_le_sum fun i _=>by unfold g f v; rw[← mul_assoc 2 (v' _ )]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right ht (by positivity))) (hh i)
       rw [← mul_sum] at hp; exact hp.trans (by linarith only[hz,hv'])
   have hyL(i : t!) : v' i.val ≤ a:=by
       have ht:= Extra.Multi.Budget.cap (hx x) {i.val}; rw [sum_singleton,if_pos (show x∈id i.val from i.property.1)] at ht; exact (le_mul_of_one_le_right ((hk _).1) (Real.one_le_exp (mul_nonneg (by linarith only [he]) (by positivity)))).trans ht
   have hR(U k)(s:t!): ‖trio R x d m J ν s U k‖ ≤ f s:=by
       unfold trio; split
       next h=> rw [norm_zero]; exact hh s
       next h' =>
         have ht:= (hk s.val).2 U _ ((actsD R x d h H hv he J ν w U k h').2); rw [abs_sub_comm] at ht; rw [Complex.norm_real]; exact (Real.abs_exp_sub_one_le (ht.trans ((hyL s).trans hv'))).trans (mul_le_mul_of_nonneg_left ht zero_le_two)
   have hp' (i:Finset t!): 0 ≤ c i:=prod_nonneg fun i _=> hh i
   refine ⟨fun i=> p*c i,fun i=> ⟨mul_nonneg hp (hp' i),fun U k=>?_⟩,?_ ⟩
   · unfold braid; rw [norm_mul,norm_prod]; exact mul_le_mul (ha _ _) (prod_le_prod (fun _ _=>norm_nonneg _) fun i _=>hR U k i) (prod_nonneg fun i _=>norm_nonneg _) hp
   let G(p:Finset t!):=∏ i∈p,g i
   have hE : ∑ i,G i ≤ Real.exp 2:=by
       unfold G; rw [← powerset_univ, ← prod_one_add]; apply le_trans _ (Real.exp_monotone hy); rw[Real.exp_sum]; apply prod_le_prod
       · intro i _; exact add_nonneg zero_le_one (mul_nonneg (hh _) (Real.exp_pos _).le)
       exact fun i _=> (add_comm ..).trans_le (Real.add_one_le_exp _)
   refine le_trans ?_ (mul_le_mul_of_nonneg_left hE (show _ from mul_nonneg hp (Real.exp_pos _).le)); rw [mul_sum]; refine sum_le_sum fun i _=>?_; unfold G g; rw [prod_mul_distrib,← Real.exp_sum,← Finset.mul_sum]
   let a':=coverNumber M! P; let b:=∑ j∈i, (coverNumber M! j.val:ℝ)
   refine le_trans (b:=p*c i*Real.exp (e*((a':ℝ)+b))) ?_ (le_of_eq ?_)
   · have hz : (coverNumber M! (widthP R x m i P):ℝ) ≤ a'+ b:=by unfold b; exact_mod_cast hT i
     exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left hz he')) (mul_nonneg hp (hp' _))
   rw [mul_add,Real.exp_add]; unfold a' b c; ring
end YM.Trace.Shepherd
