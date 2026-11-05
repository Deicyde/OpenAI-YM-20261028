import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Push.STRESS_FLUX.Color
import YM.UVNext.COUPLING_RESET.Reset




/-!
# Hessians of regular pre-mask coefficients at the flat field

Constant color invariance kills its gradient at 1;
local gauge then kills a gradient of a Lie site field in either Hessian
slot.

No continuity or polynomial approximation of a hard mask used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge} {n : Side} {p : BudgetPoint} {X : Support n}
abbrev Pot (G : Gauge) (n : Side) := Config G n → ℝ
abbrev Dir (G : Gauge) (n : Side) := Directions G n

lemma at_zero (U : Config G n) : increment U 0 = U := Work.G07.at_zero_increment _

lemma flat_ok (p : BudgetPoint) (X : Support n) : Healthy p.threshold X (1 : Config G n) := by
  simp only [Healthy,UVNext.CouplingReset.flags_one]; exact Finset.disjoint_empty_right _

abbrev germ (f : Pot G n) := f ∘ increment 1
lemma germ_diff {f : Pot G n} (h : p.Regular X f) : ContDiffAt ℝ 2 (germ f) 0 :=
  (h.smooth 1 (flat_ok p X)).of_le (show (2 : WithTop ℕ∞) ≤ p.order by
    exact_mod_cast ((by decide : 2 ≤ 6).trans p.order_ge))

def colorMove (k : G.El) : Dir G n →L[ℝ] Dir G n :=
  ContinuousLinearMap.pi (fun i => (G.adjoint k).toContinuousLinearMap ∘L ContinuousLinearMap.proj (R:=ℝ) i)
lemma exp_move (k : G.El) (u : Dir G n) : increment 1 (colorMove k u) = gauge (fun _ => k) (increment 1 u) := by
  funext e
  change G.lieExp (G.adjoint k (u e)) * 1 = k * (G.lieExp (u e) * 1) * k⁻¹
  rw [mul_one,mul_one]
  apply G.mat_injective; simp [Gauge.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl

private def edgeLane (e : Edge (Site n)) : G.Color →ₗ[ℝ] Dir G n := LinearMap.single ℝ (fun _ => G.Color) e

set_option maxHeartbeats 800000 in
lemma flat_critical (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) : fderiv ℝ (germ f) 0 = 0 := by
  let F := germ f
  have he (k : G.El) : F ∘ colorMove k = F := funext fun u => by simpa only [comp_apply, exp_move,F,germ] using h.symmetry (fun _ => k) (increment 1 u)
  have hI (k : G.El) (u : Dir G n) : fderiv ℝ F 0 (colorMove k u) = fderiv ℝ F 0 u := by
    let a := colorMove (n:=n) k
    have hh : DifferentiableAt ℝ F (a 0) := (a.map_zero.symm ▸ (germ_diff h).differentiableAt (by decide))
    have hD := ((hh.hasFDerivAt.comp 0 a.hasFDerivAt).fderiv)
    rw [he k, a.map_zero] at hD
    exact (congr($hD u)).symm
  have hz (e : Edge (Site n)) (c : G.Color) : fderiv ℝ F 0 (edgeLane e c) = 0 := by
    let L := (fderiv ℝ F 0).toLinearMap ∘ₗ edgeLane (G:=G) e
    have hl (k : G.El) (w : G.Color) : colorMove k (edgeLane e w) = edgeLane e (G.adjoint k w) := by
      funext i
      change G.adjoint k (Pi.single (M:=fun _ => G.Color) e w i) = Pi.single (M:=fun _ => G.Color) e (G.adjoint k w) i
      by_cases hi : i = e
      · subst i; simp
      simp [Pi.single_eq_of_ne hi]
    exact LinearMap.congr_fun (StressFlux.linear_invariant hG L fun k w => by
      change fderiv ℝ F 0 (edgeLane e _) = _; rw [← hl k w,hI]; rfl) c
  refine ContinuousLinearMap.ext fun u => ?_
  have hl : (∑ i : Edge (Site n), edgeLane i (u i)) = u := by
    funext j; simp [edgeLane, Finset.sum_apply,Pi.single_apply]
  change fderiv ℝ F 0 u = 0
  rw [← hl, map_sum]; simp [hz]

lemma hessian_eq (f : Pot G n) (u v : Dir G n) : logHessian f u v = fderiv ℝ (fderiv ℝ (germ f)) 0 u v := by
  exact iteratedFDeriv_two_apply ..

lemma hessian_color (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) (k : G.El) (u v : Dir G n) :
    logHessian f (colorMove k u) (colorMove k v) = logHessian f u v := by
  let a := colorMove (n:=n) k
  have he : germ f ∘ a = germ f := by
    ext w; change f (increment 1 (colorMove k w)) = _; rw [exp_move,h.symmetry]
    rfl
  have ht := (Work.F03.hessian_comp a.map_zero (germ_diff h) a.contDiff.contDiffAt (flat_critical hG h)).2 u v
  rw [he,a.fderiv] at ht
  exact ht.symm

def gradient (s : Site n → G.Color) : Dir G n := fun e => s (e.1 + step e.2) - s e.1

section GaugeChart
variable (s : Site n → G.Color)
private def twist (q : Dir G n × ℝ) := gauge (fun i => G.lieExp (-(q.2 • s i))) (increment 1 q.1)
private def chart (q : Dir G n × ℝ) : Dir G n := fun e => G.plog (G.mat (twist s q e))
private lemma twist_zero : twist s 0 = 1 := by funext i; simp [twist,Lattice.gauge,increment]
private lemma twist_jet (e : Edge (Site n)) : ContDiff ℝ ω fun q => G.mat (twist s q e) := by
  simp only [twist,Lattice.gauge,increment,G.mat_mul,G.mat_inv,Pi.one_apply,mul_one]
  have h (x : Site n) : ContDiff ℝ ω fun q : Dir G n × ℝ => G.mat (G.lieExp (-(q.2 • s x))) := G.exp_jet.comp (f:=fun q : Dir G n × ℝ => -(q.2 • s x)) (by fun_prop)
  exact ((h e.1).mul (G.exp_jet.comp ((contDiff_apply ..).comp contDiff_fst))).mul ((starL' ℝ).contDiff.comp (h _))
private lemma chart_zero : chart s 0 = 0 := by funext i; simp [chart,twist_zero]
private lemma chart_jet : ContDiffAt ℝ 2 (chart s) 0 := contDiffAt_pi.mpr fun e => by
  let v q := G.mat (twist s q e); have hz : v 0 = 1 := by simp [v, twist_zero]
  exact (ContDiffAt.comp (f:=v) (g:=G.plog) 0 (hz.symm ▸ (G.plog_diff.of_le (m:=2) le_top)) ((twist_jet s e).contDiffAt.of_le le_top))
private lemma recovered : (increment 1) ∘ chart s =ᶠ[𝓝 0] twist s := by
  have he (i : Edge (Site n)) : Tendsto (fun q => twist s q i) (𝓝 0) (𝓝 1) := by
    rw [← (show twist s 0 i = 1 by simp [twist_zero])]
    exact ((G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.isInducing.tendsto_nhds_iff.mpr
      ((twist_jet s i).continuous.tendsto _))
  filter_upwards [eventually_all.mpr fun i => (he i).eventually G.plog_right] with q hq
  funext e; change G.lieExp _ * 1 = twist s q e; rw [mul_one]; exact hq e
private lemma chart_line (q : Dir G n × ℝ) : fderiv ℝ (chart s) 0 q = q.1 + q.2 • gradient s := by
  funext i
  let pr := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ : Edge (Site n) => G.Color) i
  have h0 : pr (chart s 0) = 0 := by rw [chart_zero, map_zero]
  have ht := Gauge.expDiff_zero G
  have he := ht.comp_hasDerivAt_of_eq 0 (pr.hasFDerivAt.comp_hasDerivAt 0
    (Push.side (chart s) ((chart_jet s).differentiableAt (by decide)) q)) (by simpa using h0.symm)
  have hh : HasDerivAt (fun t : ℝ => G.mat (twist s (t • q) i)) (G.colorMat (fderiv ℝ (chart s) 0 q i)) 0 := by
    refine he.congr_of_eventuallyEq ?_
    have hc : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 0) := by simpa using! (continuous_id.smul continuous_const).tendsto' (0:ℝ) 0 (zero_smul ℝ q)
    filter_upwards [hc.eventually (recovered s)] with t ht
    congr 1
    exact (show G.lieExp _ * 1 = _ from congr_fun ht i) ▸ (mul_one _)
  apply G.colorMat_injective
  refine hh.unique ?_
  have hX (a : G.Color) : HasDerivAt (fun t : ℝ => G.mat (G.lieExp (t • a))) (G.colorMat a) 0 := by
    have h := hasDerivAt_id' (0:ℝ) |>.smul_const a; simpa only [one_smul] using! ht.comp_hasDerivAt_of_eq 0 h (zero_smul ..).symm
  have h := ((hX (-(q.2 • s i.1))).mul (hX (q.1 i))).mul (hX (-(q.2 • s (i.1 + step i.2)))).star
  simp only [twist, Lattice.gauge, increment, Pi.one_apply,mul_one,G.mat_mul,G.mat_inv,Prod.smul_fst,Prod.smul_snd,
    Pi.smul_apply,smul_eq_mul, ← smul_smul, ← smul_neg]
  convert! h using 1 <;> simp [gradient,G.colorMat_skew,smul_sub] <;> abel
end GaugeChart

lemma hessian_gradient (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) (s : Site n → G.Color) (u : Dir G n) :
    logHessian f (gradient s) u = 0 := by
  let π := ContinuousLinearMap.fst ℝ (Dir G n) ℝ
  let F := germ f
  have hC := flat_critical hG h
  have he : F ∘ chart s =ᶠ[𝓝 0] F ∘ π := by
    filter_upwards [recovered s] with q hq
    exact (congrArg f hq).trans (show f (twist s q) = f (increment 1 q.1) from h.symmetry ..)
  let a : Dir G n × ℝ := (0,1); let b : Dir G n × ℝ := (u,0)
  have hh := (Work.F03.hessian_comp (chart_zero s) (germ_diff h) (chart_jet s) hC).2 a b
  have hi := (Work.F03.hessian_comp π.map_zero (germ_diff h) π.contDiff.contDiffAt hC).2 a b
  rw [(he.iteratedFDeriv ℝ 2).self_of_nhds, hi, chart_line,chart_line,π.fderiv] at hh
  simp only [a,b,π,ContinuousLinearMap.coe_fst', one_smul,zero_smul,zero_add,add_zero] at hh
  exact hh.symm.trans (by simp [iteratedFDeriv_two_apply])

lemma hessian_diag (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) (v : Dir G n) :
    logHessian f v v = leftDerivs f [v,v] 1 := by
  have ht := Work.F03.line_second (germ_diff h) (flat_critical hG h) v
  have he := Next.Foundations.leftDerivs_diag 1 v f 2 0
  rw [zero_smul,at_zero] at he
  exact ht.symm.trans he.symm

lemma hessian_symm {f : Pot G n} (h : p.Regular X f) (v w : Dir G n) : logHessian f v w = logHessian f w v :=
  Work.F03.hessian_symmetric (germ_diff h) ..

lemma hessian_agrees (hG : G.Simple) {f : Pot G n} (h : p.Regular X f) {a b c d : Dir G n}
    (hab : Agrees X a b) (hcd : Agrees X c d) : logHessian f a c = logHessian f b d := by
  have he {u v : Dir G n} (hv : Agrees X u v) : logHessian f u u = logHessian f v v := by
    have ht := germ_diff h
    have hg := flat_critical hG h
    unfold logHessian
    change iteratedFDeriv ℝ 2 (germ f) 0 _ = iteratedFDeriv ℝ 2 (germ f) 0 _
    rw [← Work.F03.line_second ht hg u, ← Work.F03.line_second ht hg v]
    exact congrArg (iteratedDeriv 2 · 0) <| funext fun t => h.sites _ _ fun i hi hx =>
      congrArg (fun w => G.lieExp (t • w) * 1) (hv i hi hx)
  have hh := he (show Agrees X (a+c) (b+d) from fun i hi hx => congrArg₂ (· + ·) (hab i hi hx) (hcd i hi hx))
  simp_rw [hessian_eq] at hh
  simp only [map_add, add_apply] at hh
  simp_rw [← hessian_eq] at hh; rw [he hab,he hcd,hessian_symm h c a,hessian_symm h d b] at hh
  linarith only [hh]
end YM.AnalyticBridge.VerifiedReset
