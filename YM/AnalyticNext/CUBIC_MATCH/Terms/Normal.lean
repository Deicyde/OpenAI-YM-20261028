import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import YM.AnalyticNext.CUBIC_MATCH.Rays
import YM.Pressure.Seeds
import YM.Work.F02.Series



set_option warningAsError false

/-!
# Term extraction on actual path series

We exploit the several-variable local bound on true path monomials from F02 to
upgrade to normal convergence for ALL finite terms in the germ. Then extract
even after a curved real path substitution (will finally use only order three).
Pay the positive radius -- can't do this in just finite differentiability by
quoting an unweighted real sum. Width assertions for the cubic payment are
separate; this identification doesn't itself need period-uniform constants.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function Metric ContinuousMultilinearMap Work.F02
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius

variable {ι E F Z : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {u : ι → ℝ} {f : ι → E → F} {z : E} {R : ℝ}
section complex
variable [CompleteSpace F]

lemma normal_series (k : ℕ) (hR : 0<R) (hf : ∀ i, ContDiff ℂ ω (f i)) (hu : Summable u)
    (h : ∀ i x, x∈ball z R → ‖f i x‖ ≤ u i) : ∃ r : ℝ, 0<r ∧ ∃ v : ι → ℝ, Summable v ∧
      ∀ x∈ball z r, (∀ i, ‖iteratedFDeriv ℂ k (f i) x‖ ≤ v i) ∧
        HasSum (fun i => iteratedFDeriv ℂ k (f i) x) (iteratedFDeriv ℂ k (fun x => ∑' i,f i x) x) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ _
  induction k with
  | zero =>
    refine ⟨R,hR,u,hu,fun x he => ⟨?_,?_⟩⟩
    · intro i; simpa only [norm_iteratedFDeriv_zero] using h i x he
    have hx : Summable (fun i => f i x) := .of_norm_bounded hu (fun i => h i x he)
    simp only [iteratedFDeriv_zero_eq_comp, comp_apply]; exact
      (continuousMultilinearCurryFin0 ℂ E F).symm.toContinuousLinearEquiv.toContinuousLinearMap.hasSum hx.hasSum
  | succ k IH =>
    obtain ⟨r,hr,v,hv,H⟩ := IH
    let a := r/2; have ha : 0<a := half_pos hr
    have ha' : a<r := half_lt_self hr
    let L (i) := iteratedFDeriv ℂ k (f i)
    have hl (i) : Differentiable ℂ (L i) := (hf i).differentiable_iteratedFDeriv (by simp)
    let w i := v i / a; have hw : Summable w := by simp only [w,div_eq_mul_inv]; exact hv.mul_right _
    have hg (i) (x) (hx : x∈ball z a) : ‖fderiv ℂ (L i) x‖ ≤ w i := fderiv_bound (hl i) hr (fun y g => (H y g).1 i) hx
    refine ⟨a,ha,w,hw,fun x hx => ⟨fun i => ?_,?_⟩⟩
    · rw [iteratedFDeriv_succ_eq_comp_left,comp_apply,LinearIsometryEquiv.norm_map]; apply hg i x hx
    simp only [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    have he := hasFDerivAt_tsum_of_isPreconnected hw isOpen_ball (convex_ball z _).isPreconnected
      (fun i y _ => ((hl i) y).hasFDerivAt) hg (mem_ball_self ha) (H z (mem_ball_self hr)).2.summable hx
    have hh : iteratedFDeriv ℂ k (fun x => ∑' i,f i x) =ᶠ[𝓝 x] fun y => ∑' i,L i y := by
      filter_upwards [isOpen_ball.mem_nhds (ball_subset_ball ha'.le hx)] with i hi
      exact (H i hi).2.tsum_eq.symm
    rw [hh.fderiv_eq,he.fderiv]; apply ContinuousLinearMap.hasSum
      (continuousMultilinearCurryLeftEquiv ℂ _ F).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ((Summable.of_norm_bounded hw fun i => hg i x hx).hasSum)
end complex

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma real_sum_terms (k : ℕ) (hR : 0<R) (hf : ∀ i, ContDiff ℂ ω (f i)) (hu : Summable u)
    (h : ∀ i x, x∈ball z R → ‖f i x‖ ≤ u i) :
    HasSum (fun i => iteratedFDeriv ℝ k (f i) z) (iteratedFDeriv ℝ k (fun x => ∑' i,f i x) z) := by
  haveI := FiniteDimensional.complete ℂ F
  obtain ⟨r,hr,a,ha,H⟩ := normal_series k hR hf hu h
  let W : (ContinuousMultilinearMap ℂ (fun _ : Fin k => E) F) →L[ℝ] Tensor.T E F k :=
    restrictScalarsLinear ℝ
  have hh := W.hasSum (H _ (mem_ball_self hr)).2
  have he : ∀ (p : E → F) (_ : ContDiffAt ℂ ω p z), W (iteratedFDeriv ℂ k p z)=iteratedFDeriv ℝ k p z :=
    fun p g => ContDiffAt.restrictScalars_iteratedFDeriv (g.of_le le_top)
  have hy := analytic_series f hR (fun i => (hf i).differentiable (by simp)) hu h
  rw [he _ hy.contDiffAt] at hh
  exact hh.congr_fun (fun i => (he _ (hf i).contDiffAt).symm)

lemma compose_series (k : ℕ) (L : F →L[ℝ] Z) (a : ℝ → E) (p : ContDiffAt ℝ ω a 0) (hR : 0<R)
    (hf : ∀ i, ContDiff ℂ ω (f i)) (hu : Summable u) (h : ∀ i x,x∈ball (a 0) R → ‖f i x‖ ≤ u i) :
    HasSum (fun i => term k (fun t => L (f i (a t)))) (term k (fun t => L (∑' i,f i (a t)))) := by
  let g (x : E) := ∑' i,f i x
  haveI := FiniteDimensional.complete ℂ F
  have hh : ContDiffAt ℝ ω g (a 0) := (analytic_series f hR (fun i => (hf i).differentiable (by simp)) hu h).contDiffAt.restrict_scalars ℝ
  have he (c : OrderedFinpartition k) : HasSum (fun i => iteratedFDeriv ℝ c.length (f i) (a 0)
      fun j ↦ iteratedDeriv (c.partSize j) a 0)
      (iteratedFDeriv ℝ c.length g (a 0) fun j ↦ iteratedDeriv (c.partSize j) a 0) :=
    ContinuousMultilinearMap.hasSum_eval (real_sum_terms _ hR hf hu h) _
  have hb (i) : ContDiffAt ℝ ω (f i) (a 0) := (hf i).contDiffAt.restrict_scalars ℝ
  have hx : HasSum (fun i => term k (f i ∘ a)) (term k (g ∘ a)) := by
    unfold term; apply HasSum.const_smul
    rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hh p le_top]; simp_rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition (hb _) p le_top]
    exact hasSum_sum (s:=Finset.univ) (fun c _ => he c)
  change HasSum _ (term k (fun t => L ((g ∘ a) t)))
  rw [term_linear L ((hh.comp _ p).of_le le_top)]
  apply (L.hasSum hx).congr_fun; intro i
  exact term_linear L (((hb i).comp _ p).of_le le_top)
end YM.CubicMatch
