import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import YM.Analysis.Weak
import YM.UVExtension.Lamppost.Parade

/-!
Transporting tests down the manufacturing line. The real theorem is to bound the
receipt on the span of the actual probes. This will include uses where geometric
branch rules were only certified on real unmasked germs. Doesn't require Banach
currency be consumed upstream/don't strengthen to complex G. Constructions need
not send unit balls onto unit balls. No separability of `K` in readings.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Complex Filter Metric Topology Set BoundedContinuousFunction
open scoped BigOperators ContDiff Classical
variable {A Z K B : Type*} {M U : ℝ} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
lemma canal [TopologicalSpace K] {f:Z → K →ᵇ ℂ} {S : Set Z} (h : ∀ k,Bumps S (fun z=> f z k))
    (hp : ∀ x∈ S,∀ i,‖f x i‖ ≤ M) (hm:0≤M): Bumps S f:= by
  intro s g hs he hk; let v z:= f (g z)
  let k (i:K): (K→ᵇ ℂ)→L[ℂ] ℂ:= BoundedContinuousFunction.evalCLM ℂ i
  have hV i := h i _ g hs he hk
  refine (YM.Analysis.lift_weak (range k) ?_ hs ?_ ?_).differentiableOn
  · intro u v h; exact DFunLike.ext _ _ fun i=> h (k i) (mem_range_self i)
  swap
  · rintro _ ⟨i,rfl⟩; exact hV i
  intro z hz
  change ContinuousWithinAt v s z
  apply ContinuousAt.continuousWithinAt
  obtain ⟨r,hr,hR⟩:= nhds_basis_closedBall.mem_iff.mp (hs.mem_nhds hz)
  let d:= r/2; have hd :0<d:=half_pos hr
  have he' : ContinuousOn v (ball z d):= by
    let c: NNReal:= ⟨M/d,div_nonneg hm hd.le⟩
    refine (show LipschitzOnWith c v _ from lipschitzOnWith_iff_dist_le_mul.mpr ?_).continuousOn
    have hE u (hu:u∈ ball z d) : closedBall u d ⊆ s := by
      intro x hx; apply hR; rw [mem_ball] at hu; rw [mem_closedBall] at hx ⊢; unfold d at *; linarith [dist_triangle x u z]
    intro x hx y hy
    simp only [dist_eq_norm]; apply (BoundedContinuousFunction.norm_le (show 0≤ _ from by positivity)).2; intro i
    change ‖(v x) i - (v y) i‖ ≤ _
    have hg q (h : q∈ball z d): q∈s:= hE q h (mem_closedBall_self hd.le)
    refine (convex_ball z d).norm_image_sub_le_of_norm_deriv_le (f:=fun x=> v x i) (fun z hz=> (hV i).differentiableAt (hs.mem_nhds (hg z hz))) ?_ hy hx
    intro z h; rw [← cderiv_eq_deriv hs (show DifferentiableOn ℂ (fun x=> v x i) s from hV i) hd (hE z h)];
    exact norm_cderiv_le hd (fun u hu=> hp (g u) (he (hE _ h (sphere_subset_closedBall hu))) i)
  exact he'.continuousAt (ball_mem_nhds z hd)

section lift
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] {L : Type*} [NormedAddCommGroup L] [NormedSpace ℂ L]

lemma finance (f:Y →ₗ[ℂ] L) (p:Y→ₗ[ℂ] ℂ) (h:∀ y, ‖p y‖ ≤ M*‖f y‖) (hm:0≤M) :
    ∃ F:L →L[ℂ] ℂ, ‖F‖≤M∧∀ x,F (f x)=p x:= by
  have he : LinearMap.ker f≤LinearMap.ker p:= by
    intro x hx; have hh:f x=0:= hx; change p x=0; apply norm_le_zero_iff.mp; simpa [hh] using h x
  let g := ((LinearMap.ker f).liftQ p he).comp f.quotKerEquivRange.symm.toLinearMap
  have hg x (h : f x∈ LinearMap.range f) : g ⟨f x,h⟩=p x:= by
    unfold g; simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  have hL (x): ‖g x‖ ≤ M* ‖x‖:=by
    rcases x with ⟨x,y,hy⟩; subst x; rw [hg]; exact h y
  let G:= g.mkContinuous M hL
  obtain ⟨F,hF,hr⟩:= exists_extension_norm_eq _ G
  exact ⟨F,hr.trans_le (G.opNorm_le_bound hm hL),fun x=> (hF ⟨f x,by simp⟩).trans (hg _ _)⟩
end lift

-- use any real test currency uniform (input hol bound M still varies over geography)
lemma bloom {T : Set Z} {x : A→ Z} {src : A→K→ℝ} {f:Z→ K→ ℂ} (hx:∀ i,x i∈T) (he : ∀ i,Bumps T (fun z=>f z i)) (hF : ∀ i k,f (x i) k=↑(src i k))
    (g:A→ℝ) (hf : ∀ (s:Finset A) (h:A→ℝ) (n:ℝ),0≤n → (∀ i,‖∑ k∈s,h k*src k i‖≤n)→ ‖∑ k∈s,h k*g k‖ ≤ M*n)
    (hm:0≤ M) {b:Z→ℝ} (hy : ∀ z∈T,0 ≤ b z ∧ (b z ≤ U ∧ 0≤U) ∧ ∀ k, ‖f z k‖ ≤ b z) (hr:0≤U) :
    ∃ D:Z→ℂ, Bumps T D ∧ (∀ i,D (x i)=↑(g i))∧∀ z∈T,‖D z‖≤2*M*b z:=by
  letI : TopologicalSpace K:=⊥; letI : DiscreteTopology K:= discreteTopology_bot _
  let G (z) := if h:z∈T then ofNormedAddCommGroupDiscrete (f z) (b z) ((hy z h).2.2) else (0: K →ᵇ ℂ)
  have hG(z)(h:z∈T): (⇑(G z))= f z := by dsimp only [G]; rw [dif_pos h]; rfl
  have hg : Bumps T G:= canal (M:=U) (fun i W h hw he' ht=> (he i W h hw he' ht).congr (fun y hy=> by change G (h y) i=f (h y) i; rw [hG _ (he' hy)])) (fun z hz i=> by rw [hG z hz]; exact ((hy z hz).2.2 _).trans (hy z hz).2.1.1) hr
  let F:= Finsupp.linearCombination ℂ (G ∘ x)
  let H:= Finsupp.linearCombination ℂ (Complex.ofReal ∘ g)
  have hp(v:A →₀ ℂ):‖H v‖≤ 2*M*‖F v‖:= by
    have hv(i):F v i=∑ j∈v.support,v j*(src j i:ℂ):= by
      let L: (K→ᵇ ℂ) →L[ℂ] ℂ := evalCLM ℂ i; change L (F v) = _; unfold F; rw [Finsupp.linearCombination_apply, Finsupp.sum,map_sum]; apply Finset.sum_congr rfl; intro j _; exact Eq.trans (L.map_smul ..) (congr_arg (v j * ·) ((congr_fun (hG _ (hx j)) i).trans (hF j i)))
    have ht:H v=∑ j∈v.support, v j*(g j:ℂ):= rfl
    have hI : ‖∑ j∈v.support, (v j).re*g j‖≤ M*‖F v‖ := by
      refine hf _ _ _ (norm_nonneg _) (fun i=> ?_); have h := (Complex.abs_re_le_norm (F v i)).trans ((F v).norm_coe_le_norm i); rw [hv] at h; simpa using h
    have hj : ‖∑ j∈v.support, (v j).im*g j‖ ≤ M*‖F v‖:=by
      refine hf _ _ _ (norm_nonneg _) (fun i=> ?_); have h := (Complex.abs_im_le_norm (F v i)).trans ((F v).norm_coe_le_norm i); rw [hv] at h; simpa using h
    rw [ht]; apply Complex.norm_le_abs_re_add_abs_im _|>.trans; simp only [re_sum,im_sum,mul_re,mul_im,ofReal_im,ofReal_re,mul_zero,sub_zero,zero_add];
    exact (add_le_add hI hj).trans_eq (by ring)
  obtain ⟨C,hC,h⟩:= finance F H hp (by positivity)
  refine ⟨C∘ G, fun s f hs he hf=> C.differentiable.comp_differentiableOn (hg s f hs he hf),fun i=> ?_,fun z hz=> ?_⟩
  · simpa [F,H] using h (Finsupp.single i 1)
  apply (C.le_opNorm ..).trans
  exact mul_le_mul hC ((BoundedContinuousFunction.norm_le (hy z hz).1).mpr fun i=> (by rw [hG _ hz]; exact (hy _ hz).2.2 _)) (norm_nonneg _) (by positivity)
end YM.UVExtension.Lamppost
