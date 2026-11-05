import YM.FullVolume.Canvas.Angles
/-! Atom score priced, Jet sensitivity with fixed sorted.Write for limits. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Shade
open Filter Set Function lp Lattice Laurent Bloch Exterior RG Precision Wilson Tralis
open scoped Topology BigOperators InnerProductSpace ContDiff Matrix.Norms.Frobenius NNReal ENNReal
variable {G:Gauge}{t:ℕ}[NeZero t]{m:Side}{σ:ℝ}
private lemma read_value (h:0<σ)(U:Config G m) : ∃ S:Cameo G t→L[ℝ] ℝ,∀ x,S x= uncut (ringT σ x) U :=by
    let f(x:Cameo G t) (i)(r:Site m):= (ringT σ x i).unmasked U r
    have hp (r x) : RG.SumBudget (fun i=> |f x i r|) (credits G t (σ-0)*‖x‖*2^(t+1)):=by
        let W := fun i=> (ringT σ x i).budget 0
        have hw:= radius σ x h ‖x‖ le_rfl
        refine Work.F08.budget_minor (g:=fun i=> W i*2^(t+1)) ?_ (fun i=> abs_nonneg _) (fun i=>?_)
        · exact ⟨fun i=>mul_nonneg (hw.1 i) (by positivity),hw.2.1.mul_right _,by unfold W; rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hw.2.2 (by positivity)⟩
        apply le_trans ((ringT σ x i).unmasked_bound U r); unfold W; simp only [Atom.budget,zero_mul,Real.exp_zero,mul_one]; exact le_rfl
    have H (r:Site m) : ∃ S:Cameo G t→L[ℝ] ℝ,∀ x,S x=∑' i,f x i r:=by
        have hh x : Summable fun i=> f x i r:=Summable.of_norm (show Summable (fun i=>‖f x i r‖) from (hp r x).2.1)
        let L:Cameo G t→ₗ[ℝ] ℝ:={ toFun:=fun x=>∑' i,f x i r,
                                      map_add':=fun x y=>by
                                         rw [← (hh x).tsum_add (hh y)]
                                         refine tsum_congr fun i=>?_ ; simp [f,Atom.unmasked,Atom.poly,ringT,add_div,add_mul, Finset.sum_add_distrib],
                                      map_smul':=fun c x=>by
                                         rw [RingHom.id_apply,smul_eq_mul,← tsum_mul_left]; refine tsum_congr fun i=> ?_; simp [f,Atom.unmasked,Atom.poly,ringT, mul_div_assoc,Finset.mul_sum,mul_assoc] }
        have hk x : ‖L x‖ ≤ (credits G t (σ-0)*2^(t+1))*‖x‖:= (norm_tsum_le_tsum_norm (show Summable (fun i=> ‖f x i r‖) from (hp r x).2.1)).trans (by rw [mul_right_comm]; exact (hp r x).2.2)
        exact ⟨LinearMap.mkContinuous L _ hk,fun _=>rfl⟩
    choose S HS using H; exact ⟨∑ i,S i,fun x=> by simp only [_root_.sum_apply,HS, uncut]; rfl⟩
lemma fibres (h:0<σ)(i:ℕ): ∃ S:Cameo G t→L[ℝ] Tensor.T (Link G m) ℝ i,∀ x,S x= iteratedFDeriv ℝ i (turnSeries (ringT σ x)) 0 :=by
   refine Tralis.starlight (f:=fun e:Cameo G t=> turnSeries (ringT σ e) (m:=m)) (fun x=>?_) (fun e=>turns_analytic _ (show 0<σ/2 by linarith) (radius σ e (show σ/2<σ by linarith) ‖e‖ le_rfl)) i
   choose D Hd using fun i:Signed=> read_value (t:=t) h (pull i 0 (input G m x))
   refine ⟨(Fintype.card Signed:ℝ)⁻¹ • ∑ i,D i,fun i=>?_⟩; simp only [_root_.smul_apply,_root_.sum_apply,Hd,turnSeries,Patch.average]; rfl
lemma shineN {x:Cameo G t}(h:0<σ):
    AnalyticAt ℝ (turnSeries (ringT σ x) (m:=m)) 0:= turns_analytic _ (show 0 < σ/2 by positivity) (radius σ _ (show σ/2<σ by linarith) ‖x‖ le_rfl)
lemma starry {ι} {S:ℕ→ Cameo G t}{X b}(h:0<σ)(Y:Gleam S X b): Tendsto (fun i=>iteratedFDeriv ℝ ι (turnSeries (ringT σ (S i)) (m:=m)) 0) atTop (𝓝 (iteratedFDeriv ℝ ι (turnSeries (ringT σ X)) 0)):=by
   obtain ⟨F,hF⟩:= fibres (G:=G) (t:=t) (m:=m) h ι; simp_rw [←hF]; exact Y.vectors F
end YM.Stationary.Shade
