import YM.FullVolume.Ray.Rebar
/-! Exact converse with radius loss. Vector Banach completion germ! -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Ray.Rebar
open Filter Set Function RG Push.AbsoluteSums ContinuousLinearMap
open scoped Topology BigOperators NNReal ENNReal ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p c : ℝ} {f : ℝ → E}
lemma linear_snapshot (h:Rebar p f c) (hp:1<p) : ∃ L : (smear p).range →L[ℝ] E, ‖L‖≤ c ∧∀ w:Rung,L ((smear p).rangeRestrict w)= trace w f:=by
  let P:=smear p; let F:Rung →ₗ[ℝ] E:= Finsupp.linearCombination ℝ (fun i:sun=> f i.val)
  have hB (w:Rung):‖F w‖≤ c*‖P w‖ := by
    rw [mul_comm]; apply h.beam w; intro i
    have hh:(P w) i=trace w (fun x=>(x/p)^i):=by
      unfold P smear trace; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_smul,Pi.smul_apply,fil hp]
    rw [← hh]; exact lp.norm_apply_le_norm (by simp) _ _
  let g:= P.rangeRestrict
  obtain ⟨b,hb⟩:= LinearMap.exists_rightInverse_of_surjective g (LinearMap.range_eq_top.mpr P.surjective_rangeRestrict)
  have hh x: P (b x) = x.val:= congr_arg Subtype.val (DFunLike.congr_fun hb x)
  let L:= F.comp b
  have hk x: ‖L x‖≤ c*‖x‖ := (hB _).trans_eq (congr_arg (fun x'=>c*‖x'‖) (hh x))
  refine ⟨L.mkContinuous c hk, LinearMap.mkContinuous_norm_le _ h.nonneg hk,?_⟩
  intro w; change F (b (g w))=F w; have he:= hB (b (g w)-w); rw [map_sub,map_sub,hh] at he; rw [show (g w).val=P w from rfl, sub_self,norm_zero,mul_zero] at he; exact sub_eq_zero.mp (norm_le_zero_iff.mp he)
lemma recovery [CompleteSpace E] (h:Rebar p f c) {a:ℝ} (ha:1≤a) (hp:a<p) : Scout a f ((1-a/p)⁻¹*c):=by
  have hr:=ha.trans_lt hp; have h':=zero_lt_one.trans hr; have hh:= zero_lt_one.trans_le ha
  obtain ⟨L,hL,ht⟩:= linear_snapshot h hr
  let X:=spans p; let Y:=(smear p).range
  have hK : Y≤X:=Y.le_topologicalClosure
  let q:Y→ₗ[ℝ] X:= Submodule.inclusion hK; have hu z: ‖q z‖≤1*‖z‖:= by rw [one_mul]; rfl
  let V:= q.mkContinuous 1 hu; have hV:DenseRange V:=by
    intro x; apply Metric.mem_closure_iff.2; intro ε he
    obtain ⟨k,hk,hp⟩:= Metric.mem_closure_iff.1 (show x.val∈closure (Y:Set Wire) from x.property) ε he
    exact ⟨_,⟨⟨k,hk⟩,rfl⟩,show dist x (V ⟨k,hk⟩) < ε from hp⟩
  let P:= ContinuousLinearMap.extend L V
  have hv : ‖P‖≤c := by
    refine (opNorm_extend_le L (N:=1) hV (fun i=> by rw [NNReal.coe_one,one_mul]; exact le_rfl)).trans ?_
    simpa
  let d(i:ℕ):X:=⟨single i,speck hr i⟩; have hk i: ‖d i‖=1:= points i
  let r:=a/p; have hy:0<r:= div_pos hh h'; have hr':r<1:= (div_lt_one h').mpr hp
  let b i := r^i • P (d i)
  have hc i: ‖b i‖ ≤ r^i*c := by
    unfold b; rw [norm_smul, norm_pow,Real.norm_of_nonneg hy.le]; apply mul_le_mul_of_nonneg_left _ (pow_nonneg hy.le _)
    refine (P.le_opNorm _).trans ?_; rwa [hk,mul_one]
  have hs := (hasSum_geometric_of_norm_lt_one (ξ:=r) (by rw [Real.norm_of_nonneg hy.le]; exact hr')).mul_right c
  refine ⟨ha,b,budget_mono (budget_loosen (f:=_) ⟨(fun i=>mul_nonneg (pow_nonneg hy.le i) h.nonneg),hs.summable,hs.tsum_eq.le⟩ le_rfl) (fun _=>norm_nonneg _) hc,?_⟩
  intro x hx; let i:sun:= ⟨x,hx⟩; let h:=Finsupp.single i (1:ℝ); let y: Y:= (smear p).rangeRestrict h
  have hm : IsClosed (X:Set Wire) := Y.isClosed_topologicalClosure
  letI : CompleteSpace X:= hm.isComplete.completeSpace_coe
  let v(j:ℕ):= (x/p)^j • d j; have hz : Summable v:= by
    apply Summable.of_norm; dsimp only [v]; simp_rw [norm_smul,norm_pow,hk,mul_one]; exact summable_geometric_of_lt_one (norm_nonneg _) (radius hr i)
  have he : P (V y)=f x:=by
    unfold P; rw [ContinuousLinearMap.extend_eq L hV ((show Isometry V from fun _ _=> rfl).isUniformInducing),ht]; simp [trace,h,i] -- L y issue
  have hh : ∑' i,v i=V y:=by
    apply Subtype.ext
    calc _ = _ := ((X.subtypeL.hasSum hz.hasSum).tsum_eq).symm
         _ = _ := Eq.symm (show (V y).val=wire p i from start _ i)
  rw [← he,← hh]; apply (P.hasSum hz.hasSum).congr_fun
  intro i; unfold b v; simp_rw [map_smul, smul_smul,← mul_pow]; rw [show x/a*r=x/p from by unfold r; field_simp]
end YM.FullVolume.Ray.Rebar
