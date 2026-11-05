import YM.Planned.PRIMARY_INTEGRAL_295.Porous


/-!
# Same-chart integration authority for E.Jpr Gaussian smooth piece

Use `Regales` with all requests at threshold equality etc. Moving B
support/coupling make no uniform-radius assumption at this node: only
whether the envelope Occurs in volume can be taken under the integral.
No exchanging masks. Supper uses arbitrary bounds depending period/card,
not used as prices. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Porous
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place Emits Ripple
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius NNReal ENNReal
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {S : Finset Cover} {k l n : ℕ} {t ξ s M : ℝ}

section Part
variable {F Y G' : Type*}
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G'] [NormedSpace ℝ G'] {f : F × Y → G'}

def vertical (f : F × Y → G') (n : ℕ) (x : F × Y) := iteratedFDeriv ℝ n (fun y:Y=> f (x.1,y)) x.2

private lemma parcel {x : F × Y} (hq:ContDiffAt ℝ k f x) (hn:n≤k) :
    vertical f n x=(iteratedFDeriv ℝ n f x).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ F Y) := by
  classical
  let L:=ContinuousLinearMap.inr ℝ F Y
  have hN : (n:WithTop ℕ∞)≤(k:WithTop ℕ∞) := Nat.cast_le.mpr hn
  have he : ContDiffAt ℝ n (fun z => f (x+z)) 0 := by
    have hh : ContDiffAt ℝ n f (x+0) := by rw [add_zero]; exact hq.of_le hN
    exact hh.comp (f:=fun z=> x+z) 0 (contDiffAt_const.add contDiffAt_id)
  have hv := Next.Foundations.jets_linear L he
  rw [iteratedFDeriv_comp_add_left, add_zero] at hv
  unfold vertical
  let g : Y→G':=fun y=>f (x.1,y)
  have he' : ((fun z:F×Y => f (x+z)) ∘ L)=fun w:Y=> g (x.2+w) := by funext w; rcases x with ⟨p,q⟩; simp [g,L]
  rw [he', iteratedFDeriv_comp_add_left,add_zero] at hv; exact hv

lemma vert_cont {x : F × Y} (hq:ContDiffAt ℝ k f x) (hn:n≤k) :
    ContinuousAt (vertical f n) x := by
  let L:=ContinuousMultilinearMap.compContinuousLinearMapL
     (F:=G') (f:=fun _ : Fin n => ContinuousLinearMap.inr ℝ F Y)
  have he := L.continuous.continuousAt.comp (show ContinuousAt (iteratedFDeriv ℝ n f) x from
      hq.continuousAt_iteratedFDeriv (Nat.cast_le.mpr hn))
  exact he.congr_of_eventuallyEq ((hq.eventually (by simp)).mono fun v hv=>parcel hv hn)
end Part

namespace Stand
variable (h : Stand I E S G) (B : Roof S G) {Q:E→Dev S G} (hc : h.Calls B Q t ξ s k M)
include hc
private lemma newborn : ∀ᶠ x in 𝓝 (0:E),∀ u:Sky I, ContDiffAt ℝ k (uncurry h.rho) (u,x) ∧
    ContDiffAt ℝ k (uncurry (h.skyW B ξ t)) (u,x) := by
  filter_upwards [hc.serve.1.eventually (by simp),hc.crown.1.eventually (by simp)] with y hd hh u
  let a:=(u,y)
  have hb : ContDiffAt ℝ k (fun x : Sky I×E => h.square x.2 x.1) a :=
    (hh.comp (f:=Prod.snd) a contDiffAt_snd).clm_apply contDiffAt_fst
  refine ⟨hc.profile.1.contDiffAt.comp a hb,?_⟩
  have he : ContDiffAt ℝ k (uncurry (h.bed ξ)) a := by
    refine (hd.comp (f:=Prod.snd) a contDiffAt_snd).add ?_
    exact (h.breeze.contDiff.contDiffAt.comp a hb).const_smul _
  unfold skyW
  exact ((B.smooth.of_le (m:=(k:WithTop ℕ∞)) (by exact_mod_cast le_top)).contDiffAt.comp
    (f:=fun v:Sky I×E=> t • h.bed ξ v.1 v.2) a (he.const_smul _)).const_smul _
lemma weightJoint (u:Sky I) : ContDiffAt ℝ k (uncurry h.rho) (u,0) := (mem_of_mem_nhds (h.newborn B hc) u).1

-- all-real normalized cost test

def candle (B : Roof S G) (ξ t : ℝ) (f : Dev S G→ℂ) (l : ℕ) := Emits.atom (h.skyW B ξ t) h.rho f l t

private lemma burns (f : Dev S G→ℂ) (hf:ContDiff ℝ ω f) : ∀ᶠ x in 𝓝 (0:E), ∀ u:Sky I,
    ContDiffAt ℝ k (uncurry (h.candle B ξ t f l)) (u,x) := by
  apply (h.newborn B hc).mono; intro x hh u
  have he := Tones.coat_smooth hf l t
  exact (hh u).1.smul ((he.of_le le_top).contDiffAt.comp (u,x) (hh u).2)

-- Need also moving chart support even off-centermass. B inverse need not
-- meet the forecast prices for this proof. Γ subset tested in Sky coordinates.
private lemma locks : ∃ N : ℝ, ∀ᶠ a in 𝓝 (0:E),∀ x:Sky I, N<‖x‖ → M < ξ * ‖h.square a x‖ := by
  obtain ⟨D,hD,hd⟩:=hc.invert
  let C:=1+D; have hC : 1≤C := le_add_of_nonneg_right hD
  have hp : 0<ξ:=hc.noise.1
  have he := (hc.crown.1.continuousAt.tendsto.eventually (ball_mem_nhds (h.square 0) (show 0 < (2*C)⁻¹ by positivity)))
  refine ⟨M/ξ*(2*C),?_⟩
  filter_upwards [he] with a ha x hx
  have he : 2*C *((2*C)⁻¹)=1 := mul_inv_cancel₀ (by positivity)
  have hh : ‖h.square 0 x‖ ≤ ‖h.square a x‖ + (2*C)⁻¹*‖x‖ := by
    rw [add_comm]
    apply (norm_le_norm_sub_add _ (h.square a x)).trans
    have ht : ‖h.square 0 - h.square a‖≤ (2*C)⁻¹ := by rw [← dist_eq_norm,dist_comm]; exact (mem_ball.mp ha).le
    exact add_le_add_left (((h.square 0-h.square a).le_opNorm x).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))) _
  have hf : ‖x‖ ≤ C*(‖h.square a x‖ + (2*C)⁻¹*‖x‖) := (hd x).trans (mul_le_mul
    (le_add_of_nonneg_left zero_le_one) hh (norm_nonneg _) (zero_le_one.trans hC))
  have hw' : M/ξ*(2*C) < ‖h.square a x‖*(2*C) := by
    have h1 := congr_arg (· * ‖x‖) he
    nlinarith only [h1,hx,hf]
  have hw : M/ξ < ‖h.square a x‖ := lt_of_mul_lt_mul_right hw' (by positivity)
  rw [mul_comm ξ]; exact (div_lt_iff₀ hp).mp hw

variable [FiniteDimensional ℝ E]

/-- Can indeed feed Ripple/Supper path integral apparatus. -/
lemma clocks (f : Dev S G→ℂ) (hf:ContDiff ℝ ω f) (l : ℕ) : Regales (h.candle B ξ t f l) (stdGaussian (Sky I)) k 0 := by
  classical
  obtain ⟨N,H⟩:= h.locks B hc
  obtain ⟨r,hr,h'⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp ((h.burns B hc f hf (l:=l)).and H)
  let s:= closedBall (0:E) r; let S:=ball (0:E) r; let g:=h.candle B ξ t f l
  let v (n : ℕ) := vertical (uncurry g) n
  have he : IsOpen S := isOpen_ball
  have hz (p:Sky I×E) (hp : p.2∈s) : ContDiffAt ℝ k (uncurry g) p := (h' hp).1 _
  have hY (n : ℕ) (hn:n≤k) (p:Sky I×E) (hp : p.2∈s) := vert_cont (hz p hp) hn
  have hd (n : ℕ) (hn:n≤k) (y : E) (hy : y∈s) : AEStronglyMeasurable (report g n y) (stdGaussian (Sky I)) := by
    have he : Continuous (report g n y) := continuous_iff_continuousAt.mpr fun i=> (hY n hn (i,y) hy).comp (f:=fun z:Sky I=>(z,y))
       (show ContinuousAt (fun z:Sky I=>(z,y)) i from continuousAt_id.prodMk continuousAt_const)
    exact he.aestronglyMeasurable
  have hy (y:E) (p:Sky I) (hY:y∈S) (hp:N<‖p‖) (n:ℕ) : report g n y p=0 := by
    have he' : g p =ᶠ[𝓝 y] 0 := by
      filter_upwards [he.mem_nhds hY] with z hz
      have hx := (hc.cover (h.square z p)).2.2 ((h' (ball_subset_closedBall hz)).2 p hp)
      simp only [g,candle,Emits.atom,rho,hx,zero_smul]; rfl
    unfold report; rw [(he'.iteratedFDeriv ℝ _).self_of_nhds]; simp
  refine ⟨S,mem_ball_self hr,he,Eventually.of_forall (fun z y hy=> ?_),fun n hn y hy=>hd _ hn _ (ball_subset_closedBall hy),fun n hn=>?_⟩
  · exact (hz (z,y) (ball_subset_closedBall hy)).comp (f:=fun u:E=>(z,u)) y (contDiffAt_const.prodMk contDiffAt_id)
  letI:= FiniteDimensional.proper ℝ E
  let T := closedBall (0:Sky I) N ×ˢ s
  have ht : IsCompact T := (isCompact_closedBall ..).prod (isCompact_closedBall ..)
  obtain ⟨C,hC⟩:= ht.bddAbove_image (f:=fun x=> ‖v n x‖) (show ContinuousOn (fun x=>‖v n x‖) T from
    fun x hx=>((hY n hn x hx.2).norm.continuousWithinAt))
  refine ⟨fun _=>max 0 C,integrable_const _,Eventually.of_forall fun z y hY'=>?_⟩
  by_cases hp : ‖z‖≤N
  · exact (show ‖v n (z,y)‖≤C from hC ⟨(z,y),⟨by simpa using hp,ball_subset_closedBall hY'⟩,rfl⟩).trans (le_max_right ..)
  rw [show report _ n y z=_ from hy y z hY' (lt_of_not_ge hp) n,norm_zero]; exact le_max_left ..
end Stand
end YM.Planned.PrimaryIntegral295.Porous
