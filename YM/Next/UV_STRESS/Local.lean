import YM.Next.UV_STRESS.Weak
import YM.Work.B10

/-!
# Uniform local jets from descendant bounds in distributions

On a diagonal ultraviolet comparison curve with derivative labels, the order-zero
bound is available also for every fixed descendant. Here is the compact upgrade
via localization and Fourier inversion, a route without point-transfer on the
shrinking k-grid. No bound at infinity or on contact tests required. On the
other hand this takes more than just convergence distributionally of the
kernels under consideration! Applies even on collinear windows and at arity 0.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Measure Analysis
open scoped Topology FourierTransform ContDiff InnerProductSpace BigOperators
variable {n : ℕ} {K : ℕ → Points n → ℂ}

lemma norm_wave (x y : Points n) : ‖Dash.wave x y‖=1 := by
  rw [Dash.wave,Complex.norm_exp]; simp

abbrev scan (f : Test n) (K : Points n → ℂ) : Points n → ℂ :=
    𝓕 (fun x => f x*K x)

/-- Taking every frequency at once costs only a bounded sup norm of the tests. -/
lemma scan_uniform (h : Fades K) (t : Test n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ i, ‖scan t (K k) i‖ ≤ ε := by
  obtain ⟨M,hM,hv⟩ := test_bounded t
  filter_upwards [h.reads _ t.hasCompactSupport t.tsupport_subset M hM _ he] with k hk i
  obtain ⟨y,hy⟩ := Dash.extend t (Dash.enough i)
  have hz : scan t (K k) i = y.applyTo (K k) := by
    rw [scan,Dash.scanned,Test.applyTo]; simp_rw [show ∀ u,y u=Dash.wave i u*t u from fun u => congr_fun hy u, mul_assoc]
  have hp : tsupport y ⊆ tsupport t := closure_mono (show support ⇑y ⊆ support ⇑t from by
    intro x hx he; apply hx; rw [show y x=Dash.wave i x*t x from congr_fun hy x, show t x=0 from he,mul_zero])
  rw [hz]
  apply hk y hp
  intro x; rw [show y x=Dash.wave i x*t x from congr_fun hy x,norm_mul,norm_wave,one_mul]; exact hv _

/-- Abstract scalar family cost. `step` allows replacing a gradient exactly
on Conf with another member, eventually. The data are used to prove bounds,
not infer existence of a hierarchy. -/
structure GradientFamily (P : (ℕ → Points n → ℂ) → Prop) : Prop where
  entry K : P K → Fades K
  step K : P K → ∀ (p : Fin n) (a : Axis), ∃ H, P H ∧
    ∀ᶠ k in atTop, EqOn (Points.gradient p a (K k)) (H k) (conf n)

namespace GradientFamily
variable {P : (ℕ → Points n → ℂ) → Prop} (h : GradientFamily P)
include h

lemma vanishing (ht : P K) (t : Test n) (p : Fin n) (a : Axis) (m : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ x : Points n, (Boundary.Probe.q*|x p a|)^m * ‖scan t (K k) x‖ ≤ ε := by
  induction m generalizing K ε t with
  | zero => simpa using scan_uniform (h.entry _ ht) t he
  | succ m ih =>
    obtain ⟨H,hH,hE⟩ := h.step K ht p a
    filter_upwards [ih hH t (half_pos he), ih ht (Dash.down t p a) (half_pos he), hE] with k hk hr hx x
    let f := scan t (H k)
    let F := scan t (K k)
    let g := scan (Dash.down t p a) (K k)
    have hy := Dash.iter (K k) (H k) ((h.entry _ ht).loc _) p a (fun T => by
      rw [← Test.apply_eq T hx]; exact Dash.compactTest ((h.entry _ ht).smooth k) T p a) x t
    let q := Boundary.Probe.q* |x p a|
    have hq : 0 ≤ q := mul_nonneg Boundary.Probe.qpos.le (abs_nonneg _)
    have hp : q*‖F x‖ ≤ ‖f x‖ + ‖g x‖ := le_trans (b:=‖f x+g x‖) (by
      unfold f g scan; rw [← hy]
      simp [q,F,scan,abs_of_nonneg Boundary.Probe.qpos.le]) (norm_add_le ..)
    change q^(m+1) * ‖F x‖ ≤ ε
    rw [pow_succ,mul_assoc]
    apply (mul_le_mul_of_nonneg_left hp (pow_nonneg hq _)).trans
    rw [mul_add]; exact (add_le_add (hk x) (hr x)).trans_eq (add_halves _)

lemma radial (ht : P K) (t : Test n) (m : ℕ) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ x : Points n, ‖x‖^m * ‖scan t (K k) x‖ ≤ ε := by
  classical
  cases n with
  | zero =>
    have hz := h.entry _ ht
    filter_upwards [scan_uniform hz t he] with k hk x
    cases m with
    | zero => simpa using hk x
    | succ m => simp [show x = 0 from Subsingleton.elim _ _, he.le]
  | succ n =>
    let X := Fin (n+1) × Axis
    let Y : ℝ := Fintype.card X
    let A := (Y/Boundary.Probe.q)^m
    have hY : 0 < Y := Nat.cast_pos.mpr Fintype.card_pos
    have hA : 0 < A := pow_pos (div_pos hY Boundary.Probe.qpos) _
    filter_upwards [eventually_all.mpr fun i : X => h.vanishing ht t i.1 i.2 m (div_pos he hA)] with k hk x
    -- finite comparison, same Fourier coordinates as `Dash.worldwide`
    obtain ⟨b,-,hb⟩ := Finset.exists_max_image Finset.univ (fun p : X => |Points.flatten x p|) Finset.univ_nonempty
    let u := |Points.flatten x b|
    have hp : ‖x‖ ≤ Y*u := by
      let j := Points.flatten x
      let W := EuclideanSpace.basisFun X ℝ
      have hw : ∑ k : X, j k • W k=j := W.sum_repr _
      rw [← Points.flatten.norm_map x]
      change ‖j‖ ≤ _; nth_rw 1 [← hw]; apply le_trans (norm_sum_le ..)
      apply le_trans _ (show ∑ _ : X,u ≤ _ from by simp [Y]); apply Finset.sum_le_sum; intro k _
      rw [norm_smul,W.norm_eq_one,mul_one]; exact hb k (Finset.mem_univ _)
    have he : Y*u = Y/Boundary.Probe.q*(Boundary.Probe.q*|x b.1 b.2|) := by
      change Y*|x b.1 b.2|=_; field_simp [Boundary.Probe.qpos.ne']
    refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hp.trans he.le) m)
      (norm_nonneg (scan _ _ x))) ?_
    rw [mul_pow,mul_assoc]
    exact (mul_le_mul_of_nonneg_left (hk b x) hA.le).trans_eq (mul_div_cancel₀ _ hA.ne')

lemma localized (ht : P K) (t : Test n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ x ∈ conf n, ‖t x*K k x‖ ≤ ε := by
  let b := (volume (α:=Points n)).integrablePower
  let c : ℝ := 2^b * (∫ x : Points n, (1+‖x‖)^(-(b:ℝ)))
  have hv : 0 ≤ c := by dsimp only [c]; positivity
  let d : ℝ := ε/(c+1)/2
  have hd : 0 < d := by dsimp [d]; positivity
  filter_upwards [scan_uniform (h.entry K ht) t hd,h.radial ht t (0+b) hd] with k hk hr x hx
  let F (z : Points n) := t z*K k z
  let H := scan t (K k)
  have hh := (Dash.conv ((h.entry K ht).loc k) t).aestronglyMeasurable (μ:=volume)
  have hi : Integrable H := by
    refine ⟨hh,(hasFiniteIntegral_norm_iff _).mp ?_⟩
    have hz : Integrable (fun x => ‖H x‖) := by simpa only [pow_zero,one_mul] using!
      (integrable_of_le_of_pow_mul_le (μ:=volume) (f:=H) (k:=0) hk hr hh)
    exact hz.2
  have hg : F x = 𝓕 H (-x) := by
    rw [← Real.fourierInv_eq_fourier_neg]; exact (((h.entry K ht).loc k t).fourierInv_fourier_eq hi
      ((t.continuous.continuousAt).mul ((((h.entry K ht).smooth k).continuousOn x hx).continuousAt ((conf_open _).mem_nhds hx)))).symm
  change ‖F x‖ ≤ ε
  rw [hg, Dash.scanned]
  calc
    _ ≤ ∫ x, ‖H x‖ := norm_integral_le_of_norm_le hi.norm (Eventually.of_forall fun x => (by rw [norm_mul,norm_wave,one_mul]))
    _ ≤ c*(d+d) := by simpa only [pow_zero,one_mul] using!
      (integral_pow_mul_le_of_le_of_pow_mul_le (μ:=volume) (k:=0) (f:=H) hk hr)
    _ ≤ ε := by
      unfold d; rw [add_halves]
      exact (mul_le_mul_of_nonneg_right (by linarith : c ≤ c+1) (by positivity : 0 ≤ ε/(c+1))).trans_eq
        (mul_div_cancel₀ _ (by linarith : c+1≠0))

lemma uniform (ht : P K) (s : Set (Points n)) (hu : IsCompact s) (hv : s ⊆ conf n) {ε : ℝ} (he : 0<ε) :
    ∀ᶠ k in atTop, ∀ x ∈ s, ‖K k x‖ ≤ ε := by
  classical
  choose t hb using fun x : s => Dash.neighborhoodTest (hv x.property)
  choose U hU hp hz using fun x : s => mem_nhds_iff.mp (hb x)
  obtain ⟨I,hI⟩ := hu.elim_finite_subcover U hp (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hz ⟨x,hx⟩⟩)
  filter_upwards [eventually_all.mpr fun x : I => h.localized ht (t x) he] with k hk x hx
  obtain ⟨y,H,W⟩ := mem_iUnion₂.mp (hI hx)
  specialize hk ⟨y,H⟩ x (hv hx)
  simpa only [show (t y) x=1 from hU y W,one_mul] using hk

lemma jets (ht : P K) (s : Set (Points n)) (hu : IsCompact s) (hv : s ⊆ conf n) (j : ℕ) {ε : ℝ}
    (he : 0<ε) : ∀ᶠ k in atTop, ∀ x ∈ s, ‖iteratedFDeriv ℝ j (K k) x‖ ≤ ε := by
  induction j generalizing K ε with
  | zero => simpa only [norm_iteratedFDeriv_zero] using! h.uniform ht s hu hv he
  | succ j ih =>
    let X := Fin n × Axis
    let Y : ℝ := Fintype.card X
    have hy : 0 ≤ Y := Nat.cast_nonneg _
    let δ := ε/(Y+1)
    have hd : 0 < δ := by dsimp [δ]; positivity
    choose H hH hE using fun x : X => h.step K ht x.1 x.2
    filter_upwards [eventually_all.mpr (fun x => ih (hH x) hd), eventually_all.mpr hE] with k hk hm x hx
    have hp : ContDiffAt ℝ (↑(j+1 : ℕ)) (K k) x :=
      ((((h.entry _ ht).smooth k) _ (hv hx)).contDiffAt ((conf_open _).mem_nhds (hv hx))).of_le (WithTop.coe_le_coe.mpr le_top)
    have hh (i : X) : fderiv ℝ (iteratedFDeriv ℝ j (K k)) x (Points.direction i.1 i.2) =
        iteratedFDeriv ℝ j (H i k) x := by
      have he : Analysis.D (Points.direction i.1 i.2) (K k) =ᶠ[𝓝 x] H i k := by
        filter_upwards [(conf_open _).mem_nhds (hv hx)] with y hy using hm i hy
      ext u
      calc
        _ = iteratedFDeriv ℝ (j+1) (K k) x (Fin.cons (Points.direction i.1 i.2) u) := by
          rw [iteratedFDeriv_succ_apply_left,Fin.cons_zero,Fin.tail_cons]
        _ = _ := (Analysis.cons_inner hp _ _).trans (by rw [(he.iteratedFDeriv ℝ j).eq_of_nhds])
    rw [← norm_fderiv_iteratedFDeriv]
    refine (Work.B10.norm_le_direction_sum _).trans (le_trans
      (b:=∑ _ : X, δ) (Finset.sum_le_sum fun i _ => (congr_arg norm (hh i)).le.trans (hk i x hx)) ?_)
    calc
      _ = Y*δ := by simp [Y]
      _ ≤ (Y+1)*δ := mul_le_mul_of_nonneg_right (by linarith) hd.le
      _ = _ := mul_div_cancel₀ _ (by linarith)

end GradientFamily
end YM.Next.UVStress
