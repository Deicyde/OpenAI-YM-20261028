import YM.Next.EXTRACTION.Tails
import YM.Work.B06
import YM.Work.G05.Taylor

/-!
# Vanishing local jets with a ball estimate

For the initial curvature conversion at a fixed gauge image,
before coupling, order of increment chart, and torus choices. The estimates
are on local *real* germs, not on a mask.
-/

noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Function Filter
open scoped ContDiff Topology

section
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]

def FlatAt (q : ℕ) (f : E → F) (x : E) : Prop := ∀ j < q, iteratedFDeriv ℝ j f x = 0

variable {q j : ℕ} {f g : E → F} {x : E}

theorem FlatAt.comp {u : H → E} {a : H} (h : FlatAt q f (u a))
    (hf : ContDiffAt ℝ q f (u a)) (hu : ContDiffAt ℝ q u a) : FlatAt q (f ∘ u) a := by
  intro k hk
  simpa only [comp_def, Pi.zero_apply, iteratedFDeriv_fun_zero, Pi.zero_apply] using!
    (Work.G05.jets_comp (d:=k) (f:=u) (f':=u) (g:=f) (g':=(0:E → F))
      (hu.of_le (Nat.cast_le.mpr hk.le)) (hu.of_le (Nat.cast_le.mpr hk.le))
      (hf.of_le (Nat.cast_le.mpr hk.le)) contDiffAt_const rfl (fun _ _ => rfl) (fun j hj => by
        simpa using h j (lt_of_le_of_lt hj hk)) k le_rfl)

theorem FlatAt.congr (h : FlatAt q f x) (he : f =ᶠ[𝓝 x] g) : FlatAt q g x := fun j hj =>
    ((he.iteratedFDeriv ℝ j).eq_of_nhds).symm.trans (h j hj)

theorem flat_sub_taylor (f : E → F) (j : ℕ) (hf : ContDiffAt ℝ j f 0) :
    FlatAt (j+1) (f - Work.G05.blockTaylor j f) 0 := by
  intro k hk
  rw [iteratedFDeriv_sub_apply (hf.of_le (Nat.cast_le.mpr (by omega))) (Work.G05.blockTaylor_contDiff .. |>.contDiffAt),
    Work.G05.blockTaylor_jets hf k (by omega), sub_self]




theorem FlatAt.bound (h : FlatAt q f 0) (hf : ContDiff ℝ ω f) {c r : ℝ}
    (hb : ∀ x, ‖x‖ ≤ r → ‖iteratedFDeriv ℝ q f x‖ ≤ c) (hc : 0 ≤ c) :
    ∀ j ≤ q, ∀ x, ‖x‖ ≤ r → ‖iteratedFDeriv ℝ j f x‖ ≤ c * ‖x‖^(q-j) := by
  intro j hj; induction hj using Nat.decreasingInduction with
  | self => simpa using hb
  | of_succ k hk ih =>
    intro x hx
    let J := iteratedFDeriv ℝ k f
    have hm (y : E) (hy : y ∈ Metric.closedBall (0:E) ‖x‖) : ‖fderiv ℝ J y‖ ≤ c * ‖x‖ ^ (q-(k+1)) := calc
      _ = ‖iteratedFDeriv ℝ (k+1) f y‖ := by
        rw [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply, LinearIsometryEquiv.norm_map]
      _ ≤ c*‖y‖^(q-(k+1)) := ih y ((le_of_le_of_eq (by simpa using hy) rfl).trans hx)
      _ ≤ c*‖x‖^(q-(k+1)) := by gcongr; simpa using hy
    have he := (convex_closedBall (0:E) ‖x‖).norm_image_sub_le_of_norm_fderiv_le
      (fun y _ => hf.contDiffAt.differentiableAt_iteratedFDeriv (x:=y) (by simp)) hm
      (x:=0) (y:=x) (by simp) (by simp)
    rw [show q-k = (q-(k+1))+1 by omega,pow_succ,← mul_assoc]
    simpa only [h k hk,sub_zero] using! he

-- Differentiation in one input, also at a varying evaluation point in all spaces.
theorem contDiff_partial (L : H → E → F) (hL : ContDiff ℝ ω (uncurry L)) (j : ℕ) :
    ContDiff ℝ ω fun x : H × E => iteratedFDeriv ℝ j (L x.1) x.2 := by
  induction j with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hL
  | succ k ih =>
    simp_rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
    have he : ContDiff ℝ ω ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) F).symm) := by fun_prop
    refine he.comp (f:=fun x : H × E => fderiv ℝ (iteratedFDeriv ℝ k (L x.1)) x.2) ?_
    exact (ih.comp (contDiff_fst.fst.prodMk contDiff_snd)).fderiv (f:=fun x : H × E => iteratedFDeriv ℝ k (L x.1))
      contDiff_snd le_top

/-- Common vanishing-ball bound at fixed order for compact sets of external inputs. -/
theorem uniform_flat_price [FiniteDimensional ℝ E] (K : Set H) (hK : IsCompact K) (r : ℝ)
    (L : H → E → F) (hL : ContDiff ℝ ω (uncurry L)) (P : H → Prop) (q : ℕ)
    (h : ∀ a ∈ K, P a → FlatAt q (L a) 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ a ∈ K, P a → ∀ x, ‖x‖ ≤ r → ‖L a x‖ ≤ C*‖x‖^q := by
  haveI := FiniteDimensional.proper ℝ E
  obtain ⟨c,hc⟩ := (hK.prod (isCompact_closedBall (0:E) r)).bddAbove_image
    (contDiff_partial L hL q).continuous.norm.continuousOn
  refine ⟨max 1 c, one_pos.trans_le (le_max_left ..), fun a ha hA x hx => ?_⟩
  have hf : ContDiff ℝ ω (L a) := hL.comp (contDiff_const.prodMk contDiff_id)
  simpa using (h a ha hA).bound hf (fun y hy => (hc ⟨(a,y),⟨ha,Metric.mem_closedBall.mpr (by simpa using hy)⟩,rfl⟩).trans
    (le_max_right ..)) (zero_le_one.trans (le_max_left ..)) 0 (Nat.zero_le _) x hx

theorem FlatAt.partial_zero {f : E × ℝ → F} (h : FlatAt q f 0) (hf : ContDiff ℝ ω f) :
    FlatAt (q-1) (fun x : E => deriv (fun t => f (x,t)) 0) 0 := by
  intro k hk
  let a : E →L[ℝ] E × ℝ := ContinuousLinearMap.inl ℝ E ℝ
  let b : (E × ℝ →L[ℝ] F) →L[ℝ] F := ContinuousLinearMap.apply ℝ F ((0,1):E × ℝ)
  have he (x : E) : deriv (fun t : ℝ => f (x,t)) 0 = b (fderiv ℝ f (a x)) := by
    have ht := hf.differentiable (by simp) (a x)
    exact (ht.hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const 0 x).prodMk (hasDerivAt_id' (0:ℝ)))).deriv
  rw [show (fun x : E => deriv (fun t => f (x,t)) 0) = b ∘ (fderiv ℝ f ∘ a) from funext he]
  have hd := hf.fderiv_right (m:=ω) le_top
  rw [b.iteratedFDeriv_comp_left (hd.comp a.contDiff).contDiffAt le_top,
    a.iteratedFDeriv_comp_right hd _ le_top, map_zero,
    show iteratedFDeriv ℝ k (fderiv ℝ f) 0 = 0 from norm_eq_zero.mp (by
      rw [norm_iteratedFDeriv_fderiv,h (k+1) (by omega),norm_zero])]
  ext1 v
  exact map_zero b
end
end YM.WilsonStartup
