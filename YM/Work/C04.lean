import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import YM.Analysis.Polydisc
import YM.Bid.Corners


/-!
# C04: tested CR at strictly ordered time heights

Only the complex time variables are holomorphic. Use Cauchy's estimate on
one-complex-variable slices, with the *same disc radius* even as we integrate
over noncompact real position space. IBP can then use just real time line
derivatives; Schwartz decay of the test suffices (no need to first cut off
the integrals here).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.C04
open Boundary Boundary.Waves MeasureTheory Filter Set Function Metric LineDeriv Complex
open scoped Topology

variable {G : Gauge} {L : Register G} {S T : Table L} {F : Waves S}
variable {n : ℕ} {y : Heights n}

/-- Strict ordering gives a uniform positive clearance even on a neighbourhood
(not restricted to heights approaching on fixed rays). Subtract along `rate`, so
no need to take a min or choose a pair of indices; covers `n=0,1` too. -/
lemma room (hy : y ∈ east n) : ∃ k ∈ Ioc (0:ℝ) 1, ∀ᶠ u in 𝓝 y, broad u k := by
  have hc : Continuous (fun k : ℝ => y - k • rate n) := by fun_prop
  have ht : Tendsto (fun k : ℝ => y - k • rate n) (𝓝[>] 0) (𝓝 y) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ k in 𝓝[>] (0:ℝ), y - k • rate n ∈ east n :=
    ht.eventually ((open_east _).mem_nhds hy)
  obtain ⟨k, hr, hk⟩ := (he.and (show ∀ᶠ k in 𝓝[>] (0:ℝ), k ∈ Ioc 0 1 from
    Ioc_mem_nhdsGT zero_lt_one)).exists
  have hu : Continuous (fun u : Heights n => u - k • rate n) := by fun_prop
  refine ⟨k, hk, ?_⟩
  have hh : ∀ᶠ u in 𝓝 y, u - k • rate n ∈ east n :=
    (hu.tendsto y).eventually ((open_east _).mem_nhds hr)
  filter_upwards [hh] with u hu'
  simpa using begins (bigger hu') k hk.1.le

lemma bound_near (h : F.Breathes) (v : Fin n → S.Union) (hy : y ∈ east n) :
    ∃ C : ℝ, ∀ᶠ u in 𝓝 y, ∀ p, ‖F.restricted v u p‖ ≤ C := by
  obtain ⟨k, hk, he⟩ := room hy
  obtain ⟨m, C, -, hC⟩ := h n v
  exact ⟨C*k⁻¹^m, he.mono (fun u hu => hC u k hk hu)⟩

private lemma shift_strict (p : Points n) (hy : y ∈ east n) : shift p y ∈ strict n := by
  simpa using on_profile p y 1 zero_lt_one hy

lemma continuous_point (h : F.Region T) (v : Fin n → S.Union) (hy : y ∈ east n) :
    Continuous (F.restricted v y) := by
  refine continuous_iff_continuousAt.mpr (fun p => ?_)
  let g := fun x : Points n => (shift x y, Boundary.trace x)
  have hg : Continuous g := by unfold g shift Boundary.trace time spatial; fun_prop
  have hs := (h.together n v).continuousAt
    (((open_strict n).prod isOpen_univ).mem_nhds
      (show g p ∈ strict n ×ˢ univ from ⟨shift_strict p hy, mem_univ _⟩))
  exact hs.comp hg.continuousAt

lemma continuous_height (h : F.Region T) (v : Fin n → S.Union) (p : Points n)
    (hy : y ∈ east n) : ContinuousAt (fun u => F.restricted v u p) y := by
  let g := fun u : Heights n => (shift p u, Boundary.trace p)
  have hg : Continuous g := by
    have : Continuous (fun u : Heights n => shift p u) := by unfold shift; fun_prop
    exact this.prodMk continuous_const
  exact ((h.together n v).continuousAt
    (((open_strict n).prod isOpen_univ).mem_nhds
      (show g y ∈ strict n ×ˢ univ from ⟨shift_strict p hy, mem_univ _⟩))).comp hg.continuousAt

lemma bounds (h : F.Region T) (hb : F.Breathes) : F.Bounds := by
  intro n v y hy f
  obtain ⟨C, hC⟩ := bound_near hb v hy
  refine (f.integrable.norm.const_mul C).mono'
    (((continuous_point h v hy).mul f.continuous).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (mem_of_mem_nhds hC x) (norm_nonneg _)

lemma along (h : F.Region T) (hb : F.Breathes) : F.Along := by
  intro n v f y hy
  suffices ContinuousAt (fun u => F.psi v u f) y from this.continuousWithinAt
  obtain ⟨C, hC⟩ := bound_near hb v hy
  refine tendsto_integral_filter_of_dominated_convergence
    (F := fun u x => F.restricted v u x * f x)
    (bound := fun x => C*‖f x‖) ?_ ?_ (f.integrable.norm.const_mul C) ?_
  · filter_upwards [(open_east _).mem_nhds hy] with u hu
    exact (bounds h hb n v u hu f).aestronglyMeasurable
  · filter_upwards [hC] with u hu
    refine ae_of_all _ (fun x => ?_)
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hu x) (norm_nonneg _)
  exact ae_of_all _ fun x => (continuous_height h v x hy).tendsto.mul tendsto_const_nhds

/-- Increasing the real-time coordinates along `a` corresponds to moving
in the real direction in this slice; increasing the heights along `a`
corresponds to moving in the positive imaginary direction. -/
private def sliced (F : Waves S) (v : Fin n → S.Union) (y a : Heights n)
    (p : Points n) (z : ℂ) : ℂ :=
  F.restricted v (y + z.im • a) (p + z.re • dawn a)

private lemma moved (p : Points n) (y a : Heights n) (z : ℂ) :
    shift (p + z.re • dawn a) (y + z.im • a) = shift p y + z • (fun i => (a i : ℂ)) := by
  funext i
  apply Complex.ext <;> simp [shift, dawn, place, time, position]

private lemma traced (p : Points n) (a : Heights n) (t : ℝ) :
    Boundary.trace (p + t • dawn a) = Boundary.trace p := by
  funext i
  apply PiLp.ext; intro j
  simp [Boundary.trace, spatial, dawn, place, position]

private lemma diff_sliced (h : F.Region T) (v : Fin n → S.Union) (p : Points n)
    (y a : Heights n) (z : ℂ) (hz : y + z.im • a ∈ east n) :
    DifferentiableAt ℂ (sliced F v y a p) z := by
  let l := fun w : ℂ => shift p y + w • (fun i => (a i : ℂ))
  have he : sliced F v y a p = (fun w => F.F n w (Boundary.trace p) v) ∘ l := by
    funext w
    rw [sliced, restricted, moved, traced]; rfl
  have hl : l z ∈ strict n := by
    unfold l; rw [← moved]; exact shift_strict _ hz
  rw [he]; exact ((h.hol n v _).differentiableAt ((open_strict _).mem_nhds hl)).comp z
    (show DifferentiableAt ℂ l z by unfold l; fun_prop)

private lemma real_deriv (h : F.Region T) (v : Fin n → S.Union) (p : Points n)
    (hy : y ∈ east n) (a : Heights n) :
    HasLineDerivAt ℝ (F.restricted v y) (deriv (sliced F v y a p) 0) p (dawn a) := by
  have he := (diff_sliced h v p y a 0 (by simpa using hy)).hasDerivAt.scomp_of_eq 0
    (Complex.ofRealCLM.hasDerivAt (x:=0)) (by simp)
  simpa [HasLineDerivAt, Function.comp_def, sliced] using he

lemma cr_height (h : F.Region T) (v : Fin n → S.Union) (p : Points n) (y a : Heights n)
    (i : ℝ) (hi : y + i • a ∈ east n) :
    HasDerivAt (fun t : ℝ => F.restricted v (y + t • a) p)
      (I * lineDeriv ℝ (F.restricted v (y + i • a)) p (dawn a)) i := by
  let l : ℝ → ℂ := fun t => (↑t - ↑i) * I
  let u := y + i • a
  have hh : sliced F v u a p ∘ l = fun t : ℝ => F.restricted v (y + t • a) p := by
    funext t
    simp [l, sliced, u, sub_smul]
  have hd : HasDerivAt l I i := by
    simpa [l] using! (((Complex.ofRealCLM.hasDerivAt (x:=i)).sub_const (i:ℂ)).mul_const I)
  have hs := (diff_sliced h v p u a 0 (by simpa using hi)).hasDerivAt
  rw [(real_deriv h v p hi a).lineDeriv, ← hh]
  exact hs.scomp_of_eq i hd (by simp [l])

lemma deriv_bound_near (h : F.Region T) (hb : F.Breathes) (v : Fin n → S.Union)
    (hy : y ∈ east n) (a : Heights n) :
    ∃ K : ℝ, ∀ᶠ u in 𝓝 y, ∀ p,
      ‖lineDeriv ℝ (F.restricted v u) p (dawn a)‖ ≤ K := by
  obtain ⟨C, hC⟩ := bound_near hb v hy
  let l := fun q : Heights n × ℂ => q.1 + q.2.im • a
  have hc : Continuous l := by unfold l; fun_prop
  have ht : Tendsto l (𝓝 (y,0)) (𝓝 y) := by simpa [l] using hc.tendsto (y,0)
  have he : {q : Heights n × ℂ | l q ∈ east n ∧ ∀ p, ‖F.restricted v (l q) p‖ ≤ C}
      ∈ 𝓝 (y,0) := ht.eventually ((show ∀ᶠ u in 𝓝 y, u ∈ east n from
        (open_east _).mem_nhds hy).and hC)
  rw [nhds_prod_eq] at he
  obtain ⟨s, hs, t, ht', H⟩ := Filter.mem_prod_iff.1 he
  obtain ⟨r, hr, hr'⟩ := nhds_basis_closedBall.mem_iff.1 ht'
  refine ⟨C / r, ?_⟩
  filter_upwards [hs] with u hu p
  have hd z (hz : z ∈ closedBall (0:ℂ) r) :
      u + z.im • a ∈ east n ∧ ‖sliced F v u a p z‖ ≤ C := by
    have he' := H (show (u,z) ∈ s ×ˢ t from ⟨hu,hr' hz⟩)
    exact ⟨he'.1,he'.2 _⟩
  have hu' : u ∈ east n := by simpa using (hd 0 (mem_closedBall_self hr.le)).1
  have hc' : DifferentiableOn ℂ (sliced F v u a p) (closedBall (0:ℂ) r) :=
    fun z hz => (diff_sliced h v p u a z (hd z hz).1).differentiableWithinAt
  rw [(real_deriv h v p hu' a).lineDeriv]
  exact norm_deriv_le_of_forall_mem_sphere_norm_le hr (hc'.diffContOnCl_ball subset_rfl)
    (fun z hz => (hd z (sphere_subset_closedBall hz)).2)

lemma lines (h : F.Region T) (hb : F.Breathes) : F.Lines := by
  intro n v f y a i hi
  let l : ℝ → Heights n := fun t => y + t • a
  let g := fun (t : ℝ) => F.restricted v (l t)
  let d := fun (t : ℝ) (x : Points n) => lineDeriv ℝ (g t) x (dawn a)
  have hl : l i ∈ east n := hi
  obtain ⟨K, hK⟩ := deriv_bound_near h hb v hl a
  let s := {t : ℝ | l t ∈ east n ∧ ∀ x, ‖d t x‖ ≤ K}
  have hs : s ∈ 𝓝 i := ((show Continuous l by unfold l; fun_prop).tendsto i).eventually
    ((show ∀ᶠ u in 𝓝 (l i), u ∈ east n from (open_east _).mem_nhds hl).and hK)
  have hx : i ∈ s := mem_of_mem_nhds hs
  have he : Integrable (fun x => g i x * f x) := bounds h hb n v (l i) hi f
  have he' : Integrable (fun x => d i x * f x) := by
    refine (f.integrable.norm.const_mul K).mono' ((aestronglyMeasurable_lineDeriv
      (continuous_point h v hl) _).mul f.integrable.aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hx.2 x) (norm_nonneg _)
  have H : HasDerivAt (fun t : ℝ => F.psi v (y + t • a) f)
      (∫ x, I * (d i x * f x)) i := by
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun t x => g t x * f x)
      (F' := fun t x => I * (d t x * f x)) hs ?_ he ((he'.const_mul I).aestronglyMeasurable) ?_
      (f.integrable.norm.const_mul K) ?_).2
    · filter_upwards [hs] with t ht
      exact (bounds h hb n v (l t) ht.1 f).aestronglyMeasurable
    · refine ae_of_all _ (fun x t ht => ?_)
      rw [norm_mul,norm_I,one_mul,norm_mul]
      exact mul_le_mul_of_nonneg_right (ht.2 x) (norm_nonneg _)
    refine ae_of_all _ (fun x t ht => ?_)
    exact ((cr_height h v x y a t ht.1).mul_const (f x)).congr_deriv (mul_assoc ..)
  let f' := ∂_{dawn a} f
  have hp : (∫ x, g i x * f' x) = -∫ x, d i x * f x :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℂ) (v := dawn a)
      (f := g i) (g := ⇑f) (f' := d i) (g' := ⇑f') he'
      (bounds h hb n v (l i) hi f') he
      (fun x _ => (real_deriv h v x hi a).lineDifferentiableAt.hasLineDerivAt)
      (fun x _ => (f.hasFDerivAt x).hasLineDerivAt _)
  apply H.congr_deriv
  calc
    _ = - I * ∫ x, g i x * f' x := by rw [integral_const_mul, hp]; ring
    _ = ∫ x, g i x * (Waves.clock a f x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      change -I * (g i x * f' x) = g i x * (-I * f' x)
      ring
    _ = _ := rfl

theorem answer : YM.Bid.C04 := fun _ _ _ h hb =>
  ⟨bounds h hb, along h hb, lines h hb⟩

end YM.Work.C04
