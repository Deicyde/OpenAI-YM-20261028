import YM.MergeProof.North.Loon
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Float
open Function Filter Lattice Wilson RG Source Accent Push Local Extra.Histories PhysicalNext.Repeat Lotus Finset Marker Ribbon MeasureTheory
open scoped Topology BigOperators Classical
variable {ι β:Type}{G:Gauge}{n c:Side}{R:Rep G n}{κ e t z a:ℝ} {o:Site n}
local notation "P"=> R.p
lemma drift  (B:BudgetPoint)(v:ι→β)(w:β→Support n)(p:β)(f:ι→ℝ): B.mass (w p) (cram v f p) = cram v (fun i=> B.mass (w (v i)) (f i)) p:=by unfold cram BudgetPoint.mass; rw [← tsum_mul_left]; exact tsum_congr fun i=>by simp only [i.property]
lemma neigh {v:ι→β}{p:β}{f:ι→ℂ}(h:cram v f p≠ 0): ∃ i,f i≠0∧ v i=p:=by
   by_contra hn; refine h ?_; suffices hz : (fun i:{i// v i=p}=> f i.val)=0 by unfold cram; rw [hz]; exact tsum_zero
   funext i; exact Classical.byContradiction fun H=> hn ⟨_,H,i.property⟩
lemma supple [Fintype β][DecidableEq β] (f:β→ (Config G n→ℂ)):∑ i,Pi.single i (f i)=f:=by
   funext i; rw [Finset.sum_apply,Finset.sum_eq_single i]; exact Pi.single_eq_same i _; exact fun j _ hj=> Pi.single_eq_of_ne hj.symm _; simp
lemma carriage [Countable ι](A:Menu.Arsenal R)(F:ι→ Config G n→ℂ)(X:ι→ Support n)(hs:∀ i,GaugeInvariant (F i))(ht:∀ i,Measurable (F i))(ho:∀ i,o∈X i)(hf:∀ i,UsesFinal R.p.threshold (X i) (F i))(hp:∀ i U,F i U≠0→Healthy R.p.threshold (X i) U){g:ι→ℝ}(hh:∀ i U,‖F i U‖≤g i)(he:SumBudget (fun i=> R.p.mass (X i) (g i)) t): Blade R o (fun U=> ∑' i,F i U) 0 0 (2*t):=by
    let y(S:Support n) U:= cram X (fun i=>F i U) S
    have hg:= sumBudget_uncharge (fun i=>(norm_nonneg _).trans (hh i 1)) he
    have hk (S): Blade R o (y S) 0 0 (2* R.p.mass S (cram X g S)):=by
       apply petals A S _ (fun k U=>tsum_congr (fun i=>hs _ k U)) (Measurable.tsum fun i=> ht _) (fun U V h v=> tsum_congr fun i=> hf _ U V (i.property.symm ▸ h) (i.property.symm ▸ v)) (fun U h=> ?_) (fun h=>?_) (fun U=>metric_cram X hg.2.1 (fun i=> hh i U) S)
       · obtain ⟨i,h,hx⟩:=neigh (show cram X (fun i=>F i U) S≠0 from h); exact hx ▸ hp i U h
       obtain ⟨U,ht⟩:= Function.ne_iff.mp h; obtain ⟨i,h,hx⟩:= neigh (show cram X (fun i=>F i U) S≠0 from ht); exact hx ▸ ho i
    have hQ:= comp_many _ _ _ _ Finset.univ (fun i _=> hk i); simp only [Finset.sum_const_zero, ← Finset.mul_sum] at hQ
    have hf : (fun U=>∑' i,F i U)=∑ i,y i:=by funext U; have hh:= hg.2.1.of_norm_bounded (fun i=> hh i U); have hx:= (bulky X hh).tsum_eq; rw [tsum_fintype] at hx; simp only [Finset.sum_apply]; exact hx.symm
    rw [hf]; apply hQ.more; apply mul_le_mul_of_nonneg_left _ zero_le_two; have h(t:Support n): R.p.mass t (cram X g t)=cram X (fun i=>R.p.mass (X i) (g i)) t:= drift P X id t g; simp_rw [h]; have hh:=(heavy X he.2.1).tsum_eq; rw [tsum_fintype] at hh; exact hh.le.trans he.2.2
lemma punch (A:Menu.Arsenal R){F:ℕ → Config G n→ℂ}(h:ForceFormat R.p R.activities o F)(hp:ForceCost R.p R.activities F t): Blade R o 0 (profile R.activities F) 0 (2*t):=by
    obtain ⟨v,hv,hF⟩:=hp
    let Y:=barcode R.activities; let e:=profile R.activities F; let g(i):=R.p.mass (Local.patch R.activities i) (v i); have he:= sumBudget_uncharge (fun i=>(hF i).1) hv
    have ht(s:Box n): Blade R o 0 (Pi.single s (e s)) 0 (2* R.p.mass s.1 (cram Y v s)):=by
        let f:= e s
        apply pillars A _ _ (fun i U=>tsum_congr (fun j=> h.invariant _ i U)) (Measurable.tsum fun i=>h.borel _) ?_ (fun U h'=>?_) (fun h'=> ?_) (fun U=>metric_cram _ he.2.1 (fun i=>(hF i).2 _) s)
        · intro U V hp hk; apply tsum_congr; intro i; have hv:=congr_arg Prod.fst i.property
          change Local.patch R.activities i.val=s.1 at hv; exact h.supported _ U V (hv.symm ▸ hp) (hv.symm ▸ hk)
        · obtain ⟨i,hi,rfl⟩:= neigh (show cram Y (fun i=>F i U) s≠0 from h'); let x:= R.activities.forced i; exact ⟨(h.forcing _ _ hi).1, x.inventory_ne,x.inventory_sup⟩
        obtain ⟨U,hh⟩:= Function.ne_iff.mp h'; obtain ⟨i,hi,rfl⟩:=neigh (show cram Y (fun i=>F i U) s≠0 from hh); exact h.carried i (fun hx=>hi (congr_fun hx U))
    have hh:= comp_many _ _ _ _ Finset.univ (fun i _=>ht i); simp only [Finset.sum_const_zero,← Finset.mul_sum,supple] at hh
    apply hh.more; apply mul_le_mul_of_nonneg_left _ zero_le_two
    simp_rw [drift P Y Prod.fst _ v]; have hh:= (heavy Y (show Summable g from hv.2.1)).tsum_eq; rw [tsum_fintype] at hh; exact hh.le.trans hv.2.2
end YM.MergeProof.Float
