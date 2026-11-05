import YM.Dash.Twist
import YM.Extraction.Lipschitz
import YM.Shift.Cut


/-!
# Upgrade weak through-tie distribution to smooth without diagonal extraction
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Set Filter MeasureTheory Measure Complex Analysis Extraction Boundary TopologicalSpace Metric
open scoped ContDiff Topology FourierTransform InnerProductSpace BigOperators
variable {n : ℕ}

lemma full (n : ℕ) : Dense (generic n) := by
  have he := almostGeneric n
  exact dense_of_ae he

variable {K : Points n → ℂ}
lemma worldwide (h : Loc K) (hk : ∀ k : ℕ, ∀ p a,Hidden p a k K)
    (t : Test n) (w : ℕ) : ∃ C : ℝ, ∀ v : Points n, ‖v‖^w * ‖𝓕 (fun x => t x*K x) v‖ ≤ C := by
  cases n with
  | zero =>
    refine ⟨‖(0:Points 0)‖^w * ‖𝓕 (fun x => t x*K x) 0‖,fun v => ?_⟩
    simp only [show v=0 from Subsingleton.elim _ _]; rfl
  | succ n =>
    let F (v) := 𝓕 (fun x => t x*K x) v
    let X := Fin (n+1) × Axis
    choose C hC using fun p : X => hk w p.1 p.2 t
    classical
    obtain ⟨a,_,ha⟩ := Finset.exists_max_image Finset.univ C Finset.univ_nonempty
    let Y : ℝ := Fintype.card X
    refine ⟨(Y/Probe.q)^w*C a,fun i => ?_⟩
    obtain ⟨b,-,hb⟩ := Finset.exists_max_image Finset.univ (fun p : X => |Points.flatten i p|) Finset.univ_nonempty
    let u := |Points.flatten i b|
    have hp : ‖i‖≤ Y*u := by
      let j := Points.flatten i
      let P := EuclideanSpace.basisFun X ℝ
      have he : ∑ k : X, j k • P k=j := P.sum_repr _
      rw [← Points.flatten.norm_map i]
      change ‖j‖ ≤ _; nth_rw 1 [← he]; apply le_trans (norm_sum_le ..)
      apply le_trans _ (show ∑ _ : X,u ≤ _ from by simp [Y])
      apply Finset.sum_le_sum; intro k _; rw [norm_smul,P.norm_eq_one,mul_one]
      exact hb k (Finset.mem_univ _)
    have hy : Y*u=(Y/Probe.q)*(Probe.q*|i b.1 b.2|) := by change Y*|i b.1 b.2|=_; field_simp [Probe.qpos.ne']
    change ‖i‖^w * ‖F i‖ ≤ _
    calc
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hp.trans hy.le) w) (norm_nonneg (F i))
      _ ≤ _ := by
        rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left ((hC b i).trans (ha b (Finset.mem_univ _))) (pow_nonneg (div_nonneg (Nat.cast_nonneg _) Probe.qpos.le) w)

lemma conv (h : Loc K) (t : Test n) : Continuous (𝓕 (fun x => t x*K x)) := by
  apply VectorFourier.fourierIntegral_continuous _ _ (h t)
  · exact Real.continuous_fourierChar -- name
  change Continuous fun x : Points n × Points n => inner ℝ x.1 x.2; fun_prop
lemma income (h : Loc K) (hk : ∀ k : ℕ, ∀ p a, Hidden p a k K) (t : Test n) (p : ℕ) :
    Integrable (fun v => ‖v‖^p * ‖𝓕 (fun x => t x*K x) v‖) :=
  integrable_of_le_of_pow_mul_le (controls K h t)
    ((worldwide h hk t (p+(volume (α:=Points n)).integrablePower)).choose_spec) ((conv h t).aestronglyMeasurable)

theorem repair (h : Loc K) (hk : ∀ k : ℕ, ∀ p a, Hidden p a k K) (t : Test n) (hp : ContinuousOn K (generic n)) :
    ∃ g : Points n → ℂ, ContDiff ℝ ∞ g ∧ EqOn g (fun x => t x*K x) (generic n) := by
  let f (x) := t x*K x; let F := 𝓕 f
  have he : Integrable F := ⟨(conv h t).aestronglyMeasurable,(hasFiniteIntegral_norm_iff F).mp (show Integrable (fun v => ‖F v‖) from by simpa only [pow_zero,one_mul] using! income h hk t 0).2⟩
  have hh : ContDiff ℝ ∞ (𝓕 F) := Real.contDiff_fourier (fun n _ => income h hk t n)
  have hx := hh.comp (show ContDiff ℝ ∞ (fun v : Points n => -v) from contDiff_id.neg)
  refine ⟨_, hx, fun x ht => ?_⟩
  change 𝓕 F (-x)=_
  rw [← Real.fourierInv_eq_fourier_neg]; exact (h t).fourierInv_fourier_eq he
    ((t.continuous.continuousAt).mul ((hp x ht).continuousAt ((genericOpen n).mem_nhds ht)))

theorem neighborhoodTest {x : Points n} (p : x∈conf n) : ∃ g : Test n, ⇑g =ᶠ[𝓝 x] (fun _ => (1:ℂ)) := by
  obtain ⟨r,hr,hR⟩ := Metric.mem_nhds_iff.mp ((conf_open n).mem_nhds p)
  let B : ContDiffBump x := ⟨r/4,r/2,by positivity,by linarith⟩
  let u := Probe.tint B
  have he : HasCompactSupport ⇑u := by rw [HasCompactSupport,Probe.tint_support]; exact isCompact_closedBall ..
  let g : Test n := ⟨u,u.smooth ⊤,he,(by
    rw [show u=Probe.tint B from rfl,Probe.tint_support]
    exact subset_trans (Metric.closedBall_subset_ball (show r/2 < r from by linarith)) hR)⟩
  refine ⟨g,?_⟩
  filter_upwards [Metric.ball_mem_nhds x B.rIn_pos] with i hi
  change u i=1
  rw [show u i=(B i:ℂ) from rfl,B.one_of_mem_closedBall (ball_subset_closedBall hi),Complex.ofReal_one]

lemma discl {T : Set (Points n)} (hT : IsOpen T) (f g : Points n → ℂ) (hf : ContinuousOn f T) (hg : ContinuousOn g T) (h : EqOn f g (T∩generic n)) : EqOn f g T := by
  apply Measure.eqOn_open_of_ae_eq (μ:=volume) _ hT hf hg  -- μ infer?
  apply (ae_restrict_iff' hT.measurableSet).mpr
  filter_upwards [almostGeneric n] with i hi hI using h ⟨hI,hi⟩

lemma aggregate (h : Loc K) (hk : ∀ k : ℕ, ∀ p a, Hidden p a k K) (hp : ContinuousOn K (generic n)) :
    ∃ g : Points n → ℂ, ContDiffOn ℝ ∞ g (conf n) ∧ EqOn g K (generic n) := by
  classical
  have he (x : Points n) (hx : x∈conf n) : ∃ (g : Points n→ℂ) (s : Set (Points n)), x∈s ∧ s⊆conf n ∧
      IsOpen s ∧ ContDiff ℝ ∞ g ∧ EqOn g K (s∩generic n) := by
    obtain ⟨f,hf⟩ := neighborhoodTest hx
    obtain ⟨T,hT,hc,ht⟩ := _root_.mem_nhds_iff.mp hf
    obtain ⟨g,hh,hg⟩ := repair h hk f hp
    exact ⟨g,T∩conf n,⟨ht,hx⟩,inter_subset_right,hc.inter (conf_open n),hh,fun i hi => by
      rw [show g i=f i*K i from hg hi.2,show f i=1 from hT hi.1.1,one_mul]⟩
  choose F u hu hU hi hh hy using he
  let g (i : Points n) := if h : i∈conf n then F i h i else 0
  have hc (x : Points n) (hx : x∈conf n) : EqOn g (F x hx) (u x hx) := by
    intro i hI; unfold g
    let hC := hU x hx hI
    rw [dif_pos hC]
    apply discl ((hi i hC).inter (hi x hx)) _ _ (hh i hC|>.continuous.continuousOn) (hh x hx|>.continuous.continuousOn) ?_ ⟨hu i hC,hI⟩
    exact fun v hv => ((hy i hC) ⟨hv.1.1,hv.2⟩).trans ((hy x hx) ⟨hv.1.2,hv.2⟩).symm
  refine ⟨g,fun x hx => ?_,fun i hI => ?_⟩
  · exact ((hh x hx|>.contDiffAt).congr_of_eventuallyEq
      (Eventually.mono ((hi x hx).mem_nhds (hu x hx)) (fun a Ha => hc x hx Ha))).contDiffWithinAt
  let hC := generic_conf n hI
  exact (hc i hC (hu i hC)).trans (hy i hC ⟨hu i hC,hI⟩)
end YM.Dash
