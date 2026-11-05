import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Lantern.Port

/-!
# Prelog post on the actual moving station in all directions. Gross
 all orders pays parity by Mesh; only microscopic Gaussian tails and
 parameter-independent overhead not charged here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lantern
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open ConnectedActivityE6 Blaze Brush Poll Shield WithLp Matrix
open scoped Topology MatrixOrder ContDiff BigOperators Classical Interval ENNReal
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {j k : ℕ} {u d v p s A C : ℝ}
variable {ϕ ψ : E×Poll.Body ι→ℝ} {ρ : E→Poll.Body ι} {M : E → Matrix ι ι ℝ}

-- at b ≠ 0 continuity via price smooth elsewhere
variable (D : ℝ) (h : Golf ϕ ψ ρ M j D u v p)
    {x : ℝ×E} (hx : ‖x.2‖ < u) (he : ‖x.1‖ < v)
local notation "sB" => closedBall (0:Poll.Body ι) D
local notation "μ" => sweep (M 0)⁻¹
include h hx he
set_option linter.unusedSectionVars false in
lemma gallon : ContinuousOn (fun z=>grace ϕ ψ ρ M z x) sB := by
  have hy t (ht:t∈ Icc (0:ℝ) 1) (z:Poll.Body ι) : ContinuousAt (fun z=>visit ρ z t x) z := by unfold visit; fun_prop
  have hp i (hi:i ∈ Icc (0:ℝ) 1) (z:Poll.Body ι) (hz:z∈sB) := h.color z i x (mem_closedBall_zero_iff.mp hz) hi he hx
  have hψ t (ht:t∈ Icc (0:ℝ) 1) : ContinuousOn (fun z=> ψ (visit ρ z t x)) sB := fun z hz=> (((hp _ ht z hz).2.smooth.continuousAt).comp (f:=fun z=>visit ρ z t x) (hy _ ht _)).continuousWithinAt
  have hu t : ContinuousOn (fun z=> vote ϕ ρ z (0,t)) sB := by simp_rw [roll,scratch]; fun_prop
  have h' : ContinuousOn (fun z=>vote ϕ ρ z x) sB := by
    obtain ⟨b,y⟩:=x
    by_cases hb:b=0
    · subst b; exact hu y
    have hp' : ContinuousOn (fun z=>ϕ (visit ρ z 1 (b,y))) sB:= fun z hz=> (((hp 1 (by simp) z hz).1.smooth.continuousAt).comp
      (f:=fun z=>visit ρ z 1 (b,y)) (hy 1 (by simp) z)).continuousWithinAt
    apply ContinuousOn.congr ((hp'.sub (continuousOn_const (c:=ϕ (y,ρ y)))).div_const (b^2))
    intro z hz; have ht i (hi:i∈Icc (0:ℝ) 1): ContDiffAt ℝ 2 ϕ (visit ρ z i (b,y)) := (hp i hi z hz).1.smooth.of_le (by exact_mod_cast (show 2≤j+2 from Nat.le_add_left ..))
    have ht := funds ϕ ρ z b y (h.station _ hx z).1 ht; change vote ϕ ρ z (b,y) = (ϕ (visit ρ z 1 (b,y))- ϕ (y,ρ y))/b^2; rw [show visit ρ z 1 (b,y)=(y,ρ y+b • z) by simp [visit],ht]; field_simp
  exact (continuousOn_const.add ((hu 0).sub h')).add ((hψ 0 (by simp)).sub (hψ 1 (by simp)))

lemma duties : Measurable (ballots ϕ ψ ρ M D x) := by
  apply measurable_of_restrict_of_restrict_compl (s:=sB) measurableSet_closedBall
  · apply Continuous.measurable; have hp:= continuousOn_iff_continuous_restrict.mp (Real.continuous_exp.comp_continuousOn (gallon D h hx he))
    rw [show (sB).restrict (ballots ϕ ψ ρ M D x)= (sB).restrict (fun z => Real.exp (grace ϕ ψ ρ M z x)) from funext fun i=> Set.indicator_of_mem i.2 (fun z=> Real.exp (grace ϕ ψ ρ M z x))]; exact hp -- congr?
  rw [show (sB)ᶜ.restrict (ballots ϕ ψ ρ M D x)=(fun _=>0) from funext fun i=>Set.indicator_of_notMem i.2 (fun z=> Real.exp (grace ϕ ψ ρ M z x))]; exact measurable_const

omit hx he in
set_option linter.unusedSectionVars false in
lemma coming (y : E) (hy : ‖y‖<u) : ratify ϕ ψ ρ M D (0,y)=(sweep (M y)⁻¹).real sB := by
  have he : ‖(0:E)‖<u:=by rw [norm_zero]; exact h.pos
  let A:= sweep (M y)⁻¹
  have hv : A.real sB=∫ z,(sB).indicator (fun _=> (1:ℝ)) z ∂A := by simp [integral_indicator measurableSet_closedBall]
  rw [hv,ratify,recommends _ (h.gram 0 he).1.inv]; unfold A; rw [recommends _ (h.gram _ hy).1.inv]; apply integral_congr_ae; filter_upwards with z
  by_cases H:z∈sB
  · rw [ballots,Set.indicator_of_mem H, Set.indicator_of_mem H,mul_one]; apply meter; intro v hv
    have hv: ‖v‖ < u := by rcases Set.mem_insert_iff.mp hv with rfl|hv; exact he; rw [Set.mem_singleton_iff.mp hv]; exact hy
    exact ⟨(h.gram _ hv).1,fun z=> (h.station _ hv z).2⟩
  rw [ballots,Set.indicator_of_notMem H,Set.indicator_of_notMem H]; simp

variable (hj : 1 ≤ j)
include hj
omit hx he in
lemma amity (z : Poll.Body ι) (hz : ‖z‖≤D) (y : ℝ×E) (h₁: ‖y.1‖< v) (h₂ : ‖y.2‖< u) :
    |grace ϕ ψ ρ M z y| ≤ fee j p D*‖y‖ := by
  let s:= (ball (0:ℝ) v) ×ˢ ball (0:E) u
  have ht i (hi : i∈s) : Brush j (fee j p D) 1 (grace ϕ ψ ρ M z) i:= compel D h (mem_ball_zero_iff.mp hi.2) (mem_ball_zero_iff.mp hi.1) hz
  have hf i (hi:i∈s) : ‖fderiv ℝ (grace ϕ ψ ρ M z) i‖≤ fee j p D := by rw [← norm_iteratedFDeriv_one]; exact (Brush.offer.1 (ht i hi)).2 1 hj
  have he := ((convex_ball (0:ℝ) v).prod (convex_ball (0:E) u)).norm_image_sub_le_of_norm_fderiv_le (fun i hi=> (((ht i hi).smaller hj).smooth).differentiableAt (by norm_num))
    hf (show (0,(0:E))∈s from ⟨mem_ball_self h.pos',mem_ball_self h.pos⟩) (show y∈s from ⟨mem_ball_zero_iff.mpr h₁,mem_ball_zero_iff.mpr h₂⟩)
  rw [zeroC] at he; change ‖_-0‖≤_*‖y-0‖ at he; simpa only [sub_zero] using! he

variable (ha : fee j p D * max u v ≤ 1)
    (hq : ∀ y∈Set.Icc (-1:ℝ) 1, Brush j C 1 Real.exp y) (hc : 0≤C)
include ha
lemma ether (z : Poll.Body ι) (hp : ‖z‖≤D): grace ϕ ψ ρ M z x∈ Set.Icc (-1:ℝ) 1 := abs_le.mp
    ((amity D h hj z hp _ he hx).trans ((mul_le_mul_of_nonneg_left (max_le (he.le.trans (le_max_right ..)) (hx.le.trans (le_max_left ..))) (compel D h hx he hp).nonneg).trans ha)) -- order max v u!
include hq hc
lemma burs : Brush j (clump j (fee j p D) C) 1 (ratify ϕ ψ ρ M D) x ∧ Integrable (ballots ϕ ψ ρ M D x) μ := by
  have hf : ∀ᶠ y:ℝ×E in 𝓝 x, ‖y.2‖<u ∧ ‖y.1‖<v := ((continuous_norm.comp continuous_snd).continuousAt.eventually (gt_mem_nhds hx)).and
    ((continuous_norm.comp continuous_fst).continuousAt.eventually (gt_mem_nhds he))
  let V:=ballots ϕ ψ ρ M D
  let k:=clump j (fee j p D) C
  have hk : 0≤ k:= by
    have hy:‖(0:Poll.Body ι)‖ ≤ D:=by rw [norm_zero]; exact h.off
    have hh := (compel _ h hx he hy).nonneg
    unfold k clump; positivity
  have hp : ∀ᶠ y in 𝓝 x,∀ z: Poll.Body ι, Brush j k 1 (fun y=> V y z) y := by
    filter_upwards [hf] with y hy z
    by_cases H:z∈sB
    · have hz : ‖z‖ ≤ D := mem_closedBall_zero_iff.mp H -- edit
      have hx := compel D h hy.1 hy.2 hz
      exact (composite hx (hq _ (ether D h hy.1 hy.2 hj ha z hz))).shimmy (Eventually.of_forall fun i=>indicator_of_mem H _)
    exact ((Brush.certified zero_le_one (k:=j) (x:=y) (0:ℝ)).climb (by simpa using hk) le_rfl).shimmy (Eventually.of_forall fun i=> indicator_of_notMem H _)
  obtain ⟨he,hz⟩ := Meristem.points V μ ⟨fun _=> k, integrable_const _,hp⟩ (hf.mono fun i hi=>duties D h hi.1 hi.2)
  exact ⟨he.buds (fun _=> k) (integrable_const _) zero_le_one (by simp [k]) (ae_of_all _ hp.self_of_nhds),hz.self_of_nhds⟩

omit hq hc
lemma temperature (hg : Integrable (ballots ϕ ψ ρ M D x) μ) (ht : 1/2 ≤ (μ).real sB) : ratify ϕ ψ ρ M D x∈ Icc (Real.exp (-1)* (1/2)) (Real.exp 1) := by
  let f:= ballots ϕ ψ ρ M D x; let g:= grace ϕ ψ ρ M; let K:= μ
  have hp : MeasurableSet sB:= measurableSet_closedBall
  have hh z (hz:z∈sB) := ether _ h hx he hj ha z (mem_closedBall_zero_iff.mp hz)
  constructor
  · apply le_trans (mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le)
    rw [show Real.exp (-1)*K.real sB=∫ z, (sB).indicator (fun _=> Real.exp (-1)) z ∂K from by rw [integral_indicator hp]; simp; ring]
    refine integral_mono ((integrable_const _).indicator hp) hg ?_; intro z; unfold ballots; by_cases he:z∈sB
    · simp_rw [indicator_of_mem he]; exact Real.exp_monotone (hh z he).1
    simp_rw [indicator_of_notMem he]; rfl
  have hf z : f z≤ Real.exp 1 := by unfold f ballots; rw [Set.indicator]; split; exact Real.exp_monotone (hh z (by assumption)).2; exact (Real.exp_pos _).le
  exact (integral_mono hg (integrable_const _) hf).trans_eq (by simp)
variable (hw : ∀ i∈ Icc (Real.exp (-1)* (1/2)) (Real.exp 1), Brush j s 1 Real.log i)
include hw hq hc
lemma lifted (hs : 1/2 ≤ (μ).real sB) : Brush j (clump j (clump j (fee j p D) C) s) 1 (Real.log ∘ ratify ϕ ψ ρ M D) x :=
  composite (burs D h hx he hj ha hq hc).1 (hw _ (temperature D h hx he hj ha (burs D h hx he hj ha hq hc).2 hs))
end YM.PhysicalNext.Repeat.Lantern
