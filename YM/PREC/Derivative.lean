import YM.PREC.Pred

/-!
# Literal first derivative – over the physical rooted S.Predict. Every
weight after rooting. Excess centering (in uniform frame closure) doesn't
enter. No masks near trivial. Using matrix nearest projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push
open Function Set Filter Lattice RG Wilson Precision Pressure Gauge Branch Exterior Matrix
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators NNReal
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {f c : Side}

lemma travell (p : Walk) (u : Site f) (x : In G f) :
    HasDerivAt (fun v : ℝ => G.mat (travel (represent (v • x)) u p)) (G.colorMat (linkSum (collect G x) u p)) 0 := by
  exact curvature_linear G x u p

private lemma sum_sp {α : Type*} (s : Finset α) (u : α → G.Color) (i) : (∑ a∈s,u a) i=∑ a∈s,u a i := by
  let f : G.Color→ₗ[ℝ] ℝ := LinearMap.comp (LinearMap.proj i) (WithLp.linearEquiv 2 ℝ _).toLinearMap
  exact map_sum f _ _

variable (S : StepData c f)
section
variable (h : S.patch.Branches S.kernel G) (y : Site c)

def fee (u z : S.patch.Points) (o : Lattice.Order) (x : In G f) := linkSum (collect G x) (atPoint S y u) (route u.val z.val o)

def tap (u : S.patch.Points) (x : In G f) := -(avg fun z => avg fun o => fee S y u z o x)
lemma tap_line (x : In G f) (u : S.patch.Points) (j : G.ColorIndex) : tap S y u x j=tau S y u (parts G 1 x j) := by
  have ht z o : fee S y u z o x j=integralLink (atPoint S y u) (route u.val z.val o) (parts G 1 x j) := (path_component G x (atPoint S y u) _ j).symm
  simp_rw [tap,tau, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sum_apply, avg,PiLp.neg_apply,PiLp.smul_apply]
  simp_rw [sum_sp,PiLp.smul_apply,sum_sp]; simp_rw [ht,LinearMap.smul_apply,LinearMap.sum_apply]

include h
lemma derivative (t : S.SitesChoice) (v : S.patch.Points) (x : In G f) :
    HasDerivAt (fun u : ℝ => hats S y t (u • x) v) (G.colorMat (tap S y v x - tap S y S.patch.center x)) 0 := by
  let W := fun i u => hats S y t u i (G:=G)
  let d i := fderiv ℝ (W i) 0 x
  have he i : HasDerivAt (fun u : ℝ => W i (u • x)) (d i) 0 := side (W i) ((scheme S y t (h:=h) i).differentiableAt (by simp)) x
  let g (t : ℝ) := t • x
  have hh : Tendsto g (𝓝 0) (𝓝 0) := by simpa [g] using (show Continuous g by unfold g; fun_prop).tendsto 0
  have rr (i) : d i = G.lie.starProjection (avg d) + G.colorMat (tap S y i x) := by
    let f (t₀ : ℝ) := cloud S y (g t₀,hats S y t (g t₀)) i
    have hz : g 0=0:=zero_smul _ _
    have ht z o :
        HasDerivAt (fun u : ℝ => W z (g u)*star (G.mat (travel (product S y (g u)) i.val (route i.val z.val o))))
          (d z-G.colorMat (fee S y i z o x)) 0 := by
      simp_rw [product,travel_at]; let a := route i.val z.val o
      have hd := travell a (atPoint S y i) x
      have hj : HasDerivAt (fun u : ℝ => W z (g u)) (d z) 0:=he z
      convert! hj.mul hd.star using 1
      rw [hz,show W z 0=1 from hats_zero S y t (h:=h) _,G.colorMat_skew, one_mul, zero_smul,stroll_zero,mat_one,star_one,mul_one]; rfl
    have hb : HasDerivAt f (avg d + G.colorMat (tap S y i x)) 0 := by
      have he : HasDerivAt f (avg fun z => avg fun o => d z-G.colorMat (fee S y i z o x)) 0 := avg_rate _ _ _ (fun z => avg_rate _ _ _ (ht z))
      simp_rw [avg_sub,avg_const] at he
      simpa [tap, avg,map_smul,sub_eq_add_neg] using he
    have hs := focused _ hb (by unfold f; rw [hz]; exact cloud_zero S y t (h:=h) _)
    have hu : (fun a : ℝ => W i (g a)) =ᶠ[𝓝 0] fun a => G.mat (G.focus (f a)) := hh.eventually (stars S y t (h:=h) i)
    rw [map_add, Submodule.starProjection_eq_self_iff.mpr (G.colorMat_mem _)] at hs
    exact (he i).unique (hs.congr_of_eventuallyEq hu)
  have hv : d S.patch.center=0 := (he _).unique ((hasDerivAt_const (0:ℝ) (1:G.Mat)).congr_of_eventuallyEq (hh.eventually (roots S y t)))
  have hx := rr S.patch.center
  apply HasDerivAt.congr_deriv (he v)
  rw [hv] at hx
  rw [map_sub, rr v,eq_neg_of_add_eq_zero_left hx.symm]; abel
end

section
variable (h : S.patch.Branches S.kernel G) (e : Edge (Site c))

def deck (t : S.SitesChoice) (v : In G f) := S.connector (represent v) t e

def bonds (t : S.SitesChoice) (v : In G f) := ∑ i, S.patch.weight i • G.mat (deck S e t v i)

def bill (x : In G f) (i : S.patch.Points) : G.Color :=
    (tap S e.1 i x - tap S e.1 S.patch.center x) + linkSum (collect G x) (atPoint S e.1 i) (S.repath e.2) -
      (tap S (e.1+step e.2) i x - tap S (e.1+step e.2) S.patch.center x)

include h

lemma deck_zero (t : S.SitesChoice) (i) : deck S e t (0 : In G f) i=1 := by
  have he y : S.frames (represent (0:In G f)) t y i=1 := G.mat_injective (hats_zero S y t (h:=h) i)
  unfold deck StepData.connector; rw [travel_at,stroll_zero, he, he]; simp
lemma bonds_zero (t : S.SitesChoice) : bonds S e t (0 : In G f)=1 := by simp_rw [bonds, deck_zero S h e, mat_one, ← Finset.sum_smul, S.patch.weight_sum,one_smul]

lemma builds (t : S.SitesChoice) (v) : ContDiffAt ℝ ω (fun x : In G f => G.mat (deck S e t x v)) 0 := by
  unfold deck StepData.connector; simp_rw [travel_at,G.mat_mul,G.mat_inv]; apply ContDiffAt.mul
  · apply ContDiffAt.mul; exact scheme _ _ _ (h:=h) _
    exact writes _ _
  exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ (scheme _ _ _ (h:=h) _)

lemma lips (t : S.Choices) : ∀ᶠ x : In G f in 𝓝 0,
    S.prediction (represent x) t e = G.focus (bonds S e t.1 x) := by
  have hy (i) := (builds S h e t.1 i).continuousAt.tendsto
  have hS : ContinuousAt (bonds S e t.1 (G:=G)) 0 := by
    unfold bonds; apply ContDiffAt.continuousAt (𝕜:=ℝ) (n:=ω); apply ContDiffAt.sum; intro i _; exact (builds S h e t.1 i).const_smul (S.patch.weight i)
  have ht := hS.tendsto; rw [bonds_zero _ h] at ht
  have hw := S.patch.best_open (C:=S.kernel) (G:=G)
  have he : ContinuousAt (deck S e t.1 (G:=G)) 0 := continuousAt_pi.mpr fun i =>
    ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff).mpr (hy i)
  have hb : S.patch.usesBest S.kernel (deck S e t.1 (0 : In G f)) := by
    apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1)
    simpa [Patch.bondCost,deck_zero S h e t.1] using S.kernel.predictor_cut_pos
  filter_upwards [he.tendsto.eventually (hw.mem_nhds hb),ht.eventually G.nearest_is_focus] with i hi hc
  unfold StepData.prediction
  change S.patch.predict S.kernel (deck S e t.1 i) _ = _
  rw [Patch.predict, if_pos (show S.patch.usesBest _ _ from hi)]
  exact hc _ ((min_iff S.patch.weight S.patch.weight_sum _ _).2 (S.patch.bond_min _).choose_spec)

theorem settled (t : S.Choices) : S.prediction (1 : Config G f) t e=1 := by
  rw [← link_one]
  rw [mem_of_mem_nhds (lips S h e t), bonds_zero S h]
  exact (mem_of_mem_nhds G.nearest_is_focus 1 (fun i => by simp)).symm

lemma prediction_cont (t : S.Choices) : ContDiffAt ℝ ω (fun v : In G f => G.mat (S.prediction (represent v) t e)) 0 := by
  refine ContDiffAt.congr_of_eventuallyEq (f:=fun v => G.mat (G.focus (bonds S e t.1 v))) ?_ (by
    filter_upwards [lips S h e t] with i hi; rw [hi])
  have hh : ContDiffAt ℝ ω (fun u => G.mat (G.focus u)) (bonds S e t.1 (0:In G f)) := by rw [bonds_zero _ h]; exact G.focus_diff
  have he : ContDiffAt ℝ ω (bonds S e t.1 (G:=G)) 0 := by
    unfold bonds; apply ContDiffAt.sum; intro i _; exact (builds S h e t.1 i).const_smul (S.patch.weight i)
  exact hh.comp (f:=bonds S e t.1) 0 he

lemma decks (t : S.SitesChoice) (i) (x : In G f) : HasDerivAt (fun v : ℝ => G.mat (deck S e t (v • x) i)) (G.colorMat (bill S e x i)) 0 := by
  unfold deck StepData.connector bill
  simp only [travel_at,G.mat_mul,G.mat_inv]
  let a := atPoint S e.1 i
  have he y := derivative S h y t i x
  have hh : _ := ((he e.1).mul (travell (S.repath e.2) a x)).mul (he (e.1+step e.2)).star
  convert! hh using 1
  simp only [a,Pi.mul_apply,zero_smul,hats_zero S _ _ (h:=h),stroll_zero, mat_one,G.colorMat_skew, star_one,mul_one,one_mul]; simp only [map_add,map_sub]; rfl

omit h in
lemma income_eq (x : In G f) (j : G.ColorIndex) : (∑ i,S.patch.weight i • bill S e x i) j=
    ((probe S) *ᵥ parts G 1 x j) (e.1,coord e.2) := by
  classical
  rcases e with ⟨v,d⟩
  simp only [probe, Precision.mean, add_mulVec,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,bill,Pi.add_apply]
  simp only [show axisEquiv.symm (coord d)=d from axisEquiv.symm_apply_apply _, ← Matrix.mulVec_mulVec,d_sites]
  simp only [fixRoot,LinearMap.toMatrix'_mulVec,LinearMap.pi_apply,adjusted, LinearMap.sub_apply,LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [sum_sp,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,tap_line, ← path_component]
  have hl (a : Site f) w : (integralLink a w) (parts G 1 x j) = linkSum (fun e => (collect G x e).ofLp j) a w := rfl
  simp only [smul_add,smul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_smul,S.patch.weight_sum,one_smul,hl]; abel

lemma prices (t : S.Choices) (x : In G f) :
    HasDerivAt (fun v : ℝ => G.mat (S.prediction (represent (v • x)) t e)) (G.colorMat (WithLp.toLp 2 (fun j : G.ColorIndex =>
      ((probe S)*ᵥ parts G 1 x j) (e.1,coord e.2)))) 0 := by
  let d := ∑ i,S.patch.weight i • bill S e x i
  have hp : HasDerivAt (fun v : ℝ => bonds S e t.1 (v • x)) (G.colorMat d) 0 := by
    unfold bonds d; rw [map_sum]; simp only [map_smul]; apply HasDerivAt.fun_sum; intro i _
    exact (decks S h e t.1 i x).const_smul (S.patch.weight i)
  have hq := focused _ hp (by rw [zero_smul]; exact bonds_zero S h ..)
  rw [Submodule.starProjection_eq_self_iff.mpr (G.colorMat_mem _)] at hq
  have ht := lips S h e t
  rw [show WithLp.toLp _ _=d by ext i; simpa only [WithLp.ofLp_toLp] using! (income_eq S e x i).symm]
  apply hq.congr_of_eventuallyEq
  have hh : Tendsto (fun u : ℝ => u • x) (𝓝 0) (𝓝 0) := by simpa using! (show Continuous fun u : ℝ => u • x from by fun_prop).tendsto 0
  filter_upwards [hh.eventually ht] with i hi; rw [hi]
end


end YM.Push
