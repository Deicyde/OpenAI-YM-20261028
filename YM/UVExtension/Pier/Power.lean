import YM.UVExtension.Pier.Loom
/-! # Strict interior, inverse near positive point, and finite measures.
    Analytic assertion attached to the actual density; tensor operations
    use no off-real proof of the representations (nor any measurability
    continuation trick). -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Pier
open Function Filter Set Metric BoundedContinuousFunction Lattice Wilson RG
open Lamppost Rafter Complex MeasureTheory
open scoped Topology BigOperators ContDiff Classical
variable {D Z A:Type} [NormedAddCommGroup Z] [NormedSpace ℂ Z] {T:Opening D Z} {a b r:ℝ}
namespace Sail
variable {f g:D→ℂ}
lemma mult (h:Sail T f a)(he:Sail T g b)(ha:0≤a): Sail T (fun i=>f i*g i) (a*b):=by
   obtain ⟨p,hp,hP,hv⟩:= h; obtain ⟨q,hq,hQ,hA⟩:= he; exact ⟨_, bends_smul hq (f:=p) hp,fun i=>congr_arg₂ (·*·) (hP i) (hQ i),fun z hz=> (norm_mul ..).trans_le (mul_le_mul (hv z hz) (hA z hz) (norm_nonneg _) ha)⟩ -- replace
lemma within (h:Sail T f a)(d:D): ‖f d‖≤ a:=by obtain ⟨p,h,hp,he⟩:=h; rw [← hp]; exact he _ (T.within _)
lemma negative (h:Sail T f a): Sail T (fun i=> -f i) a:= by simpa using! h.scales (-1)
lemma sub (h:Sail T f a)(hf:Sail T g b): Sail T (fun i=> f i - g i) (a+b):= by simpa only [sub_eq_add_neg] using! h.plus hf.negative
lemma exp (h:Sail T f a): Sail T (fun i=> Complex.exp (f i)) (Real.exp a):= by
    obtain ⟨p,hp,hP,hv⟩:=h; refine ⟨Complex.exp ∘ p,fun s Z hs h he=> (hp s Z hs h he).cexp,fun i=>congr_arg Complex.exp (hP i),fun z hz=>?_⟩
    rw [Function.comp_apply,Complex.norm_exp]; exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (hv z hz))
lemma const (t:ℂ): Sail T (fun _=> t) ‖t‖:= ⟨fun _=>t,bumps _ _ (differentiableOn_const _),fun _=>rfl,fun _ _=>le_rfl⟩
lemma scaled (h:Sail T f a)(x:ℂ): Sail T (fun i=> f i*x) (a*‖x‖):= by simpa only [mul_comm x,mul_comm a] using h.scales x
lemma list {b:A→ℝ}{F:A→D→ℂ} (s:Finset A)(he:∀ i∈s,Sail T (F i) (b i)): Sail T (fun d=> ∑ i∈s,F i d) (∑ i∈s,b i):= by
   induction s using Finset.induction_on with
   | empty=> simpa using! const (T:=T) 0
   | @insert i s hi ih=> simp_rw [Finset.sum_insert hi]; exact (he i (Finset.mem_insert_self ..)).plus (ih fun j hj=>he j (Finset.mem_insert_of_mem hj))
section integrals
variable [MeasurableSpace A] (μ: Measure A) [IsProbabilityMeasure μ]
lemma integral {F : D→ A→ ℂ}(ha:0≤a)(h:∀ i:A,Sail T (fun d=> F d i) a)(ht:∀ i,Integrable (F i) μ) : Sail T (fun d=> ∫ x,F d x ∂μ) a:=by
   choose f hf hP hk using h
   letI : TopologicalSpace A:=⊥; letI : DiscreteTopology A:= discreteTopology_bot _
   let p(z:Z): A →ᵇ ℂ:= if hz:z∈T.span then ofNormedAddCommGroupDiscrete (fun i=> f i z) a (fun i=> hk i z hz) else 0; have hp (z)(hz:z∈T.span) i: p z i=f i z:=by unfold p; rw [dif_pos hz]; rfl
   have hx : Bumps T.span p:= canal (M:=a) (fun i s v hs hv he=> (hf i s v hs hv he).congr (fun z hz=> hp _ (hv hz) i)) (fun z hz i=>by rw [hp _ hz]; exact hk i z hz) ha
   have hQ := fun (d:D)=>p (T.call d); have he(s:Finset D)(v:D→ℂ): ‖∑i∈s,v i • ∫ x,F i x ∂μ‖≤1*‖∑ i∈s,v i • p (T.call i)‖:=by
       let R:= ∑ i∈s,v i • p (T.call i)
       have hA i: (∑ j∈s,v j • F j i)= R i:=by
          let L: (A →ᵇℂ)→L[ℂ]ℂ:= evalCLM ℂ i; change _= L R; unfold R; rw [map_sum]; refine Finset.sum_congr rfl (fun j _=>?_); rw [map_smul]; change _= v j • p _ i; rw [hp _ (T.within _),hP]
       simp_rw [smul_eq_mul,← integral_const_mul,← smul_eq_mul]; change ‖∑ i∈s, ∫ x,(v i • F i) x ∂μ‖ ≤ 1*‖∑ i∈s,v i • p (T.call i)‖; rw [← integral_finsetSum s (fun i _=> (ht i).smul (v i))]; simp only [Pi.smul_apply,hA,one_mul]; simpa using! (norm_integral_le_of_norm_le_const (μ:=μ) (Eventually.of_forall (fun i=> R.norm_coe_le_norm i)))
   obtain ⟨g,hg,hE,hL⟩:=reflectV T (fun d=>∫ x,F d x ∂μ) p hx 1 zero_le_one he
   exact ⟨g,hg,hE,fun z hz=> (hL z hz).trans ((one_mul _).trans_le ((BoundedContinuousFunction.norm_le ha).2 fun i=> (hp z hz i).symm ▸ hk i z hz))⟩
end integrals
end Sail
lemma cauchyInterior {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](f:ℂ→E)(hp:0<r)(h:DifferentiableOn ℂ f (ball 0 r))(hv:∀ z∈ ball (0:ℂ) r, ‖f z‖≤a) (x y:ℂ)(hx:x∈ball (0:ℂ) (r/3))(hy:y∈ball (0:ℂ) (r/3)): ‖f x - f y‖ ≤ a/(r/3)*‖x-y‖:=by
   let d:=r/3; have hd:0<d:=by unfold d; positivity
   have ht (z:ℂ)(h:z∈ball (0:ℂ) d): closedBall z d⊆ ball 0 r:=by intro q hq; rw [mem_ball]; have he:= mem_ball.mp h; have hv:=mem_closedBall.mp hq; unfold d at *; linarith [dist_triangle q z 0]
   exact (convex_ball (0:ℂ) d).norm_image_sub_le_of_norm_deriv_le (fun a ha=> h.differentiableAt (isOpen_ball.mem_nhds (ht _ ha (mem_closedBall_self hd.le)))) (fun z hz=>by rw [← cderiv_eq_deriv isOpen_ball h hd (ht _ hz)]; exact norm_cderiv_le hd fun q hq=> hv q (ht _ hz (sphere_subset_closedBall hq))) hy hx
lemma zeroFree (hr:0<r)(hc:0<a)(hb:0<b): ∃ t:ℝ,0<t∧ t<r∧∀ f:ℂ→ℂ,DifferentiableOn ℂ f (ball 0 r)→ (∀ z∈ball (0:ℂ) r, ‖f z‖ ≤a) → b ≤ ‖f 0‖ → ∀ z∈ ball (0:ℂ) t, b/2≤‖f z‖:= by
   let d:=r/3; have hd:0<d:=by unfold d; positivity
   let t:= min d (b/2/(a/d)); refine ⟨t,lt_min hd (by positivity), (min_le_left ..).trans_lt (by unfold d; linarith),fun f h he hq z hz=>?_⟩
   have hx:= cauchyInterior f hr h he 0 z (mem_ball_self hd) (ball_subset_ball (min_le_left ..) hz); rw [zero_sub,norm_neg] at hx
   have hv : ‖z‖*(a/d)≤ b/2:= (le_div_iff₀ (by positivity)).mp ((mem_ball_zero_iff.mp hz).le.trans (min_le_right ..)); rw [mul_comm] at hv; linarith only [hx.trans hv,hq,norm_sub_norm_le (f 0) (f z)]
end YM.UVExtension.Pier
