import YM.UVExtension.Rafter.Plier
import YM.UVExtension.Camp.Veto
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Topology Set Metric Lamppost
open scoped Topology BigOperators ContDiff Classical
variable {D U E A Z:Type} [NormedAddCommGroup U][NormedSpace ℂ U]
    [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
    [AddCommGroup A][Module ℂ A][NormedAddCommGroup Z][NormedSpace ℂ Z]
open Complex
lemma pair (T:Opening D Z){X:Type}[NormedAddCommGroup X][NormedSpace ℂ X](f g:Z→ X)(hf:Bumps T.span f)(hg:Bumps T.span g)(h:∀ i,f (T.call i)=g (T.call i))(z:Z)(hz:z∈T.span): f z=g z:=by
    apply sub_eq_zero.mp; apply tests; intro L; rw [map_sub]; apply sub_eq_zero.mpr; exact T.agrees (L ∘ f) (L ∘ g) (fun s v hs hV ht=> L.differentiable.comp_differentiableOn (hf s v hs hV ht)) (fun s v hs hV ht=> L.differentiable.comp_differentiableOn (hg s v hs hV ht)) (fun i=> congr_arg L (h i)) hz -- tests U= X maybe universe
variable (T: Opening D Z)(Y:D→ U→L[ℂ] E)(v:A→ₗ[ℂ] U)(hv:DenseRange v){c:ℝ}(hc:0≤ c)
include hv hc
lemma flick (H:∀ i:A,∃ f:Z→E,Bumps T.span f ∧ (∀ a,f (T.call a)=Y a (v i))∧∀ z∈T.span, ‖f z‖≤c*‖v i‖) : ∃ g:Z→ U→L[ℂ] E,Bumps T.span g∧ (∀ i,g (T.call i)=Y i)∧∀ z∈ T.span,‖g z‖≤c:=by
    choose f hf hT hP using H
    have hh(z:Z)(hz:z∈T.span): ∃ L:U→L[ℂ]E, ‖L‖≤ c∧∀ i:A,L (v i)=f i z:=by
        let F:A→ₗ[ℂ] E:= ⟨⟨fun i=> f i z,fun i j=>?_⟩,fun k i=>?_⟩; rotate_left
        · refine pair T (f (i+j)) (f i+f j) (hf (i+j)) (bends_add (hf i) (hf j)) (fun i=> by rw [hT,map_add,map_add,Pi.add_apply,hT,hT]) z hz
        · refine pair T (f (k • i)) (k • f i) (hf (k • i)) (fun s r hs hv h=> (hf i s r hs hv h).const_smul _) (fun i=>by rw [hT,map_smul,map_smul,Pi.smul_apply,hT]) z hz
        have hQ i: ‖F i‖≤c*‖v i‖:= hP i z hz
        exact ⟨F.extendOfNorm v,ContinuousLinearMap.opNorm_le_bound _ hc (LinearMap.norm_extendOfNorm_apply_le hv c hQ), LinearMap.extendOfNorm_eq hv ⟨c,hQ⟩⟩
    choose! g hg hL using hh
    have hF (i) : Bumps T.span (fun z=> g z (v i)):=fun s p hs hb he=> (hf i s p hs hb he).congr (fun z hz=> hL _ (hb hz) _)
    have hm(i j: U→L[ℂ] E)(hx:∀ k:A,i (v k)=j (v k)): i=j:= ContinuousLinearMap.ext (fun k=>hv.induction_on k (isClosed_eq i.continuous j.continuous) hx)
    refine ⟨g,fun s p hs hp he=> ?_,fun i=>hm _ _ (fun k=> (hL _ (T.within i) _).trans (hT ..)),hg⟩
    let P (t:A × (E→L[ℂ] ℂ)) := t.2.comp (ContinuousLinearMap.apply ℂ E (v t.1))
    let G(z):=g (p z); have hh i:= hF i s p hs hp he; apply (YM.Analysis.lift_weak (Set.range P) ?_ hs ?_ ?_).differentiableOn
    · intro i j h; exact hm i j (fun k=> sub_eq_zero.mp (tests (i (v k)-j (v k)) (fun L=> by rw [map_sub];exact sub_eq_zero.mpr (h (P (k,L)) (mem_range_self ..)))))
    swap
    · rintro _ ⟨i,rfl⟩; exact i.2.differentiable.comp_differentiableOn (hh i.1)
    intro z hz; change ContinuousWithinAt G s z; apply ContinuousAt.continuousWithinAt
    obtain ⟨t,ht,hA⟩:= nhds_basis_ball.mem_iff.mp (hs.mem_nhds hz); let d:=t/3; have hd:0<d:= by unfold d; positivity
    have he(a)(ha:a∈ball z d): closedBall a d ⊆ s:=by
         intro y hy; apply hA; rw [mem_ball]; have h:= mem_ball.mp ha; have ht:= mem_closedBall.mp hy; unfold d at *; linarith [dist_triangle y a z]
    apply ContinuousOn.continuousAt (s:=ball z d) _ (ball_mem_nhds _ hd)
    let C: NNReal:= ⟨c/d,div_nonneg hc hd.le⟩
    refine (show LipschitzOnWith C G (ball z d) from lipschitzOnWith_iff_dist_le_mul.mpr (fun x hx y hy=>?_)).continuousOn
    rw [dist_eq_norm]; let V:= G x-G y; let w:= C.val* dist x y; have hz : 0≤ w:= mul_nonneg C.2 dist_nonneg
    apply ContinuousLinearMap.opNorm_le_bound V hz; intro i; apply hv.induction_on (p:=fun i=> ‖V i‖≤w*‖i‖) i (isClosed_le V.continuous.norm (continuous_const.mul continuous_norm)); intro j
    let L(z:ℂ):= G z (v j); have H z(hz:z∈s):‖L z‖≤ c*‖v j‖:= ((g (p z)).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hg _ (hp hz)) (norm_nonneg _))
    have hf := convex_ball z d|>.norm_image_sub_le_of_norm_deriv_le (f:=L) (fun a ha=> (hh j).differentiableAt (hs.mem_nhds (he a ha (mem_closedBall_self hd.le)))) (fun a ha=> by rw [← cderiv_eq_deriv hs (show DifferentiableOn ℂ L s from hh j) hd (he a ha)]; exact norm_cderiv_le hd (fun u hu=> H u (he a ha (sphere_subset_closedBall hu)))) hy hx
    apply hf.trans; rw [← dist_eq_norm x y]; change _≤ (c/d* _)*_; apply le_of_eq; ring
end YM.UVExtension.Rafter
