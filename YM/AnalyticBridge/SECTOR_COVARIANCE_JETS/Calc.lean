import YM.Push.FREE_RESOLVENT.Envelope

set_option warningAsError false

/-!
# Ordinary jets in the exponential coordinates (calculus tools)

We will hold the sector data and the chart center V *fixed*. We want estimates
in a real neighborhood of that V, including at the center. In pricing a block
row first differentiate in one fine slot and then take the coarse derivatives.
Neither of these operations is differentiation of an indicator. The topology
on matrix spaces in these computations is Frobenius; period-uniform linear
prices use counting norms/address sums instead of Frobenius on the whole volume.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Matrix
open FreeResolvent.TestD FreeResolvent.Affine
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {E F H K : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]
variable {n m : ℕ} {C : ℝ}

/-- Vertical fderiv in a common chart. -/
def upright (f : E × F → H) (t : F) (x : E) := fderiv ℝ (fun y => f (x,y)) 0 t

lemma upright_total {f : E × F → H} {x : E} (h : DifferentiableAt ℝ f (x,0)) (t : F) :
    upright f t x = fderiv ℝ f (x,0) (0,t) := by
  let L := ContinuousLinearMap.inr ℝ E F
  have ht : HasFDerivAt (fun y : F => (x,y)) L 0 := (hasFDerivAt_const x 0).prodMk (hasFDerivAt_id _)
  unfold upright
  have he := h.hasFDerivAt.comp (f:=fun y : F => (x,y)) 0 ht
  change fderiv ℝ (f ∘ (fun y : F => (x,y))) 0 t = _
  rw [he.fderiv]; rfl

/-- Reusing global ceiling estimates without an extra Pi cardinality factor. -/
lemma upright_ceiling {f : E × F → H} (h : Ceiling (n+1) C f) (hc : 0 ≤ C)
    {t : F} (ht : ‖t‖ ≤ 1) : Ceiling n C (upright f t) := by
  let L := ContinuousLinearMap.inl ℝ E F
  let v := ContinuousLinearMap.apply ℝ H (show E × F from (0,t))
  have he : Ceiling n C (fderiv ℝ f) := by
    constructor
    · exact h.smooth.fderiv_right (by simp)
    intro j x hx; rw [norm_iteratedFDeriv_fderiv]; exact h.op (j+1) x (by omega)
  have hv : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [L]
  have hP : ‖v‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro l; refine (l.le_opNorm _).trans ?_
    have hx : ‖((0,t):E×F)‖ ≤ 1 := by simpa
    simpa using (mul_le_mul_of_nonneg_left hx (norm_nonneg l))
  have hh := ((he.pre L hc hv le_rfl).post v).mono (show ‖v‖ * (C * 1^n) ≤ C by simpa using mul_le_of_le_one_left hc hP)
  suffices hF : upright f t = fun x => v (fderiv ℝ f (L x)) by rw [hF]; exact hh
  funext x; exact upright_total (h.smooth.differentiable (by simp) _) _

/-- Convenient pointwise bounded jets, no uniformity in `AtCap` by itself. -/
structure AtCap (n : ℕ) (C : ℝ) (f : E → H) (x : E) : Prop where
  smooth : ContDiffAt ℝ n f x
  op (i : ℕ) : i ≤ n → ‖iteratedFDeriv ℝ i f x‖ ≤ C

lemma upright_event {f : E × F → H} {x : E} (h : ContDiffAt ℝ (↑(n+1):ℕ∞ω) f (x,0)) (t : F) :
    upright f t =ᶠ[𝓝 x] fun y => fderiv ℝ f (y,0) (0,t) := by
  filter_upwards [((continuous_id.prodMk (continuous_const (y:=(0:F)))).tendsto x).eventually (h.eventually (by simp))] with y hy
  exact upright_total (hy.differentiableAt (by simp)) _

lemma slide_smooth {f : H → K} (L : E →L[ℝ] H) (a : H) (x : E) {m : ℕ∞ω}
    (hf : ContDiffAt ℝ m f (a+L x)) : ContDiffAt ℝ m (fun y => f (a + L y)) x := by
  apply hf.comp x (g:=f) (f:=fun y => a + L y)
  exact contDiffAt_const.add L.contDiff.contDiffAt

/-- Composition with an affine map of genuine germs. -/
lemma slid {f : H → K} (L : E →L[ℝ] H) (a : H) (x : E)
    (hf : ContDiffAt ℝ n f (a+L x)) :
    iteratedFDeriv ℝ n (fun y => f (a + L y)) x =
      (iteratedFDeriv ℝ n f (a+L x)).compContinuousLinearMap fun _ => L := by
  let b := a+L x
  let G (y : H) := f (b+y)
  have hg : ContDiffAt ℝ n G 0 := by
    refine ContDiffAt.comp _ (g:=f) (f:=fun y => b+y) ?_ (contDiffAt_const.add contDiffAt_id)
    simpa only [add_zero] using hf
  let P y := f (a+L y)
  have hx : (fun y => P (x+y)) = G ∘ L := by
    funext y; simp only [P,G,Function.comp_apply,b,map_add,add_assoc]
  change iteratedFDeriv ℝ n P x = (iteratedFDeriv ℝ n f b).compContinuousLinearMap _
  calc
    _ = iteratedFDeriv ℝ n (fun y => P (x+y)) 0 := by rw [iteratedFDeriv_comp_add_left, add_zero]
    _ = (iteratedFDeriv ℝ n G 0).compContinuousLinearMap fun _ => L := by
      rw [hx,Next.Foundations.jets_linear L hg]
    _ = _ := by simp only [G, iteratedFDeriv_comp_add_left, add_zero]

lemma AtCap.pre {f : H → K} (L : E →L[ℝ] H) (a : H) (x : E) (h : AtCap n C f (a+L x))
    (hc : 0 ≤ C) (ht : ‖L‖ ≤ 1) : AtCap n C (fun y => f (a+L y)) x := by
  refine ⟨slide_smooth L a x h.smooth,fun i hi => ?_⟩
  rw [slid L a x (smooth_of_le h.smooth hi)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact le_trans (mul_le_mul_of_nonneg_right (h.op i hi) (pow_nonneg (norm_nonneg _) _))
    (mul_le_of_le_one_right hc (pow_le_one₀ (norm_nonneg _) ht))

lemma AtCap.post {f : E → H} (L : H →L[ℝ] K) {x : E} (h : AtCap n C f x) (hc : 0 ≤ C)
    (ht : ‖L‖ ≤ 1) : AtCap n C (fun y => L (f y)) x := by
  refine ⟨L.contDiff.contDiffAt.comp x h.smooth,fun i hi => ?_⟩
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left L h.smooth (n:=i) (by exact_mod_cast hi)).trans ?_
  refine (mul_le_mul_of_nonneg_left (h.op i hi) (norm_nonneg _)).trans (mul_le_of_le_one_left hc ht)

lemma AtCap.germ {f g : E → H} {x : E} (h : AtCap n C f x) (he : g =ᶠ[𝓝 x] f) : AtCap n C g x :=
  ⟨h.smooth.congr_of_eventuallyEq he, fun i hi => by rw [(he.iteratedFDeriv ..).eq_of_nhds]; exact h.op i hi⟩

lemma AtCap.fromCeiling {f : E → H} {x : E} (h : Ceiling n C f) : AtCap n C f x :=
  ⟨h.smooth.contDiffAt,fun i hi => h.op i x hi⟩

lemma AtCap.upright {f : E × F → H} {x : E} (h : AtCap (n+1) C f (x,0)) (hc : 0 ≤ C)
    {t : F} (ht : ‖t‖ ≤ 1) : AtCap n C (upright f t) x := by
  let L := ContinuousLinearMap.inl ℝ E F
  let v := ContinuousLinearMap.apply ℝ H (show E × F from (0,t))
  have he : AtCap n C (fderiv ℝ f) (0 + L x) := by
    rw [zero_add]; change AtCap _ _ _ (x,0)
    constructor
    · exact h.smooth.fderiv_right (by simp)
    intro i hi; rw [norm_iteratedFDeriv_fderiv]; exact h.op (i+1) (by omega)
  have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp [L]
  have hv : ‖v‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro l; refine (l.le_opNorm _).trans ?_
    have hx : ‖((0,t):E×F)‖ ≤ 1 := by simpa
    simpa using (mul_le_mul_of_nonneg_left hx (norm_nonneg l))
  refine AtCap.germ ((AtCap.pre L 0 x he hc hL).post v hc hv) ?_
  simp only [zero_add]; exact upright_event h.smooth t
end YM.AnalyticBridge.Covariance
