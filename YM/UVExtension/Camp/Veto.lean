import YM.UVExtension.Camp.Buckles
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter Metric Lamppost Complex BoundedContinuousFunction
open scoped Topology Classical BigOperators ContDiff
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℂ Y][CompleteSpace Y]
   {s:Set ℂ}(hs:IsOpen s)(hh:IsPreconnected s)

-- punch to a norm (may be infinite-dimensional even fixed volume)
include hs
private lemma holder (f:ℂ→ (ℕ→ᵇY)){M:ℝ}(hx:0≤M)(h:∀ z∈s,∀ j, ‖f z j‖≤M)(he:∀ j,DifferentiableOn ℂ (fun z=> f z j) s): DifferentiableOn ℂ f s:=by
  let k (j:ℕ): (ℕ→ᵇ Y)→L[ℂ] Y:= evalCLM ℂ j
  have hc:ContinuousOn f s:= by
    intro z hz; apply ContinuousAt.continuousWithinAt
    obtain ⟨r,hr,hR⟩:= nhds_basis_ball.mem_iff.mp (hs.mem_nhds hz)
    let d:=r/3; have hd:0<d:=by unfold d; positivity
    have hk(i)(hi:i∈ ball z d): closedBall i d⊆s:=by
        intro q hq; refine hR (mem_ball.mpr ?_); have ht:=mem_closedBall.mp hq; have hy:=mem_ball.mp hi; unfold d at *; linarith [dist_triangle q i z]
    apply ContinuousOn.continuousAt (s:=ball z d) _ (ball_mem_nhds _ hd)
    refine (show LipschitzOnWith (⟨M/d,div_nonneg hx hd.le⟩:NNReal) f (ball z d) from ?_).continuousOn
    apply LipschitzOnWith.of_dist_le_mul; intro i hi j hj; rw [dist_eq_norm,dist_eq_norm]; let H(y:Y):= y; apply (BoundedContinuousFunction.norm_le (by positivity)).2; intro x
    exact (convex_ball z d).norm_image_sub_le_of_norm_deriv_le (f:=fun v:ℂ=> f v x) (fun q hq=> (he x).differentiableAt (hs.mem_nhds (hk q hq (mem_closedBall_self hd.le)))) (fun q hq=> by rw [←cderiv_eq_deriv hs (he x) hd (hk q hq)]; exact norm_cderiv_le hd (fun a ha=> h a (hk q hq (sphere_subset_closedBall ha)) _)) hj hi
  -- separating apply HB exists_dual_vector
  let S:= ⋃ j:ℕ, (range (fun t:Y →L[ℂ] ℂ=> t.comp (k j)))
  apply AnalyticOnNhd.differentiableOn (YM.Analysis.lift_weak S ?_ hs hc ?_)
  · intro v w he; apply DFunLike.ext; intro i; by_contra h
    obtain ⟨φ,hp,hF⟩:= exists_dual_vector ℂ (v i-w i) (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))
    have ht:= he (φ.comp (k i)) (mem_iUnion.mpr ⟨i,mem_range_self _⟩)
    have hz : φ (v i-w i)=0:= by rw [map_sub]; exact sub_eq_zero.mpr ht
    rw [hz] at hF; exact (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))) hF.symm
  intro τ hi; obtain ⟨i,φ,rfl⟩:= mem_iUnion.mp hi; exact φ.differentiable.comp_differentiableOn (he i)

include hh
private lemma tale {F:ℕ→ℂ→Y}{M:ℝ}(hp:0< M)(hi:∀ i,DifferentiableOn ℂ (F i) s∧ ∀ z∈s, ‖F i z‖≤M)
    {q:ℂ}(hZ:q∈s)(ht:∀ᶠ i:ℝ in 𝓝 0,Arrives fun n=> F n (q+i)) : ∃ f,TendstoLocallyUniformlyOn F f atTop s:=by
   let f z:= if h:z∈s then ofNormedAddCommGroupDiscrete (fun i=> F i z) M (fun i=> (hi i).2 z h) else (0 : ℕ→ᵇ Y)
   have hM(z)(h:z∈s)(i): f z i=F i z:= by unfold f; rw [dif_pos h]; rfl
   have hP:= holder (hs:=hs) f hp.le (fun z hz i=> by rw [hM z hz]; exact (hi i).2 _ hz) (fun i=> (hi i).1.congr (fun z hz=> hM z hz i))
   have hy: Husk (fun f:Unit→ℕ→ᵇY=> Arrives (fun n=> f () n)):=by
     refine ⟨Arrives.steady (0:Y),fun _ _ h g=> h.plus g,fun t x h=> ?_,fun {F f} hr hs=> ?_⟩
     · exact h.post (T:=fun x:Y=> t • x) (continuous_const.smul continuous_id)
     refine trim (fun ε he=>?_); obtain ⟨n,hn,hV⟩:= ((hs ()|>.eventually (ball_mem_nhds _ he)).and hr).exists
     refine ⟨_,hV,Eventually.of_forall fun i=>?_⟩
     have hk: ‖F n ()-f ()‖≤ ε:= (dist_eq_norm (F n ()) (f ())) ▸ ((mem_ball.mp hn).le); rw [dist_comm,dist_eq_norm]; exact ((F n ()-f ()).norm_coe_le_norm i).trans hk
   have hk z (hz:z∈s):Arrives fun i=> F i z:= by
     refine (show Arrives (fun i=> f z i) from hy.invades hs hh (F:=fun z t=> f z) (fun i=> hP) hZ ?_ hz).copy (Eventually.of_forall fun i=> hM z hz i)
     have h:(fun x:ℝ=> q+ Complex.ofReal x) ⁻¹' s ∈𝓝 0:= (show Continuous (fun x:ℝ=> q+Complex.ofReal x) by fun_prop).continuousAt.preimage_mem_nhds (by simpa using hs.mem_nhds hZ)
     filter_upwards [ht,h] with i ht hs; exact ht.copy (Eventually.of_forall fun j=>(hM _ hs j).symm)
   choose! g hG using hk; refine ⟨g, Metric.tendstoLocallyUniformlyOn_iff.mpr ?_⟩; intro ε he z hz
   have he' : 0< ε/4:= by positivity
   let U:= s∩ f ⁻¹' ball (f z) (ε/4)
   refine ⟨U, Filter.inter_mem self_mem_nhdsWithin ((hP.continuousOn z hz).preimage_mem_nhdsWithin (ball_mem_nhds _ he')),?_⟩
   filter_upwards [hG z hz|>.eventually (ball_mem_nhds _ he')] with i hi x hx
   have hv : x∈s:=hx.1
   have hF j: dist (F j x) (F j z) ≤ ε/4:=by
      rw [← hM x hv,← hM z hz,dist_eq_norm]; refine le_trans ((f x-f z).norm_coe_le_norm j) ?_; exact (dist_eq_norm (f x) (f z)) ▸ (mem_ball.mp (hx.2)|>.le)
   have hy' : dist (g x) (g z)≤ε/4:= le_of_tendsto ((hG x hv).dist (hG z hz)) (Eventually.of_forall hF)
   apply lt_of_le_of_lt (dist_triangle _ (g z) _) ; rw [add_comm];
   linarith only [he, mem_ball.mp hi,hF i,hy',dist_comm (g z) (F i z),dist_comm (F i z) (F i x), dist_triangle (g z) (F i z) (F i x)]

def SummitUV (r:ℝ)(F:ℕ→ℂ→Y): Prop:= ∃ f:ℂ→ Y,AnalyticOnNhd ℂ f (ball 0 r)∧ ∀ j:ℕ, TendstoLocallyUniformlyOn (fun i=> iteratedDeriv j (F i)) (iteratedDeriv j f) atTop (ball 0 r)
omit hs hh
lemma viva {F:ℕ→ℂ→ Y} (r:ℝ)(hr:0<r)(M:ℝ)(he:∀ i,DifferentiableOn ℂ (F i) (ball 0 r) ∧ ∀ z∈ ball (0:ℂ) r, ‖F i z‖≤M)(ht:∀ x:ℝ,|x| < r → Arrives fun i=> F i x): SummitUV r F:= by
   obtain ⟨f,hF⟩:= tale isOpen_ball (convex_ball (0:ℂ) r).isPreconnected (M:=max 1 M) (by positivity) (fun i=>⟨(he i).1,fun z hz=> ((he i).2 z hz).trans (le_max_right ..)⟩) (q:=0) (mem_ball_self hr) (by
    filter_upwards [ball_mem_nhds (0:ℝ) hr] with x hx; simp only [zero_add]; exact ht _ (mem_ball_zero_iff.mp hx))
   refine ⟨_, (hF.differentiableOn (Eventually.of_forall fun i=> (he i).1) isOpen_ball).analyticOnNhd isOpen_ball,?_⟩; intro j; induction j with
   | zero=> simpa using! hF
   | succ i hi=> simp_rw [iteratedDeriv_succ]; refine hi.deriv (Eventually.of_forall fun j=> fun x hx=> ?_) isOpen_ball; rw [iteratedDeriv_eq_iterate]; exact (((he j).1.analyticAt (isOpen_ball.mem_nhds hx)).iterated_deriv i).differentiableAt.differentiableWithinAt
end YM.UVExtension.Camp
