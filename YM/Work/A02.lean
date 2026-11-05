import YM.Bid.Angular
import YM.Euclid.Window



/-!
# Moving the center inside a fixed cutoff

All identities here are for this hierarchy, with all spectators allowed. Keep χ itself fixed, so
need no step comparing cutoffs by conservation; do differentiate the *centering* in the angular
weight. Work on `conf`, using the compact support of the cutoff gradient (which misses the
insertions), so no near-diagonal extension of the kernels is being assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.A02
open Function Filter Set MeasureTheory Metric Table
open scoped Topology ContDiff BigOperators

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ} {χ : E4 → ℝ}

/-- Includes the case of no other insertions. -/
lemma exists_window {x : Points (n+1)} (hx : x ∈ conf _) : ∃ χ, Window x χ := by
  let T := Set.range (fun i : Fin n => x i.succ)
  have h : x 0 ∉ T := by
    rintro ⟨i, hi⟩
    exact i.succ_ne_zero ((show Injective x.ofLp from hx) hi)
  obtain ⟨r, hr, hT⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (show Tᶜ ∈ 𝓝 (x 0) from
      (show IsOpen Tᶜ from (finite_range _).isClosed.isOpen_compl).mem_nhds h)
  let B : ContDiffBump (x 0) := ⟨r/2, r, by positivity, by linarith⟩
  refine ⟨B, B.contDiff, B.hasCompactSupport, B.eventuallyEq_one, fun i hi => ?_⟩
  rw [B.tsupport_eq] at hi
  exact hT hi ⟨i, rfl⟩

/-- The same cutoff remains a `Window` for motion of the first point. -/
lemma stable {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (b : Axis) :
    ∀ᶠ t in 𝓝 (0 : ℝ), Ward.cast x 0 b t ∈ conf _ ∧ Window (Ward.cast x 0 b t) χ := by
  have ht : Tendsto (Ward.cast x 0 b) (𝓝 0) (𝓝 x) := by
    simpa only [ContinuousAt, Ward.start] using (Ward.moves x 0 b 0).continuousAt
  have hi := (show Continuous (fun z : Points (n+1) => z 0) from by fun_prop).continuousAt
    (x := x) |>.tendsto.comp ht
  have hχ : ∀ᶠ t in 𝓝 (0 : ℝ), χ =ᶠ[𝓝 (Ward.cast x 0 b t 0)] fun _ => 1 :=
    hi.eventually (eventually_eventuallyEq_nhds.mpr hw.2.2.1)
  filter_upwards [ht ((conf_open _).mem_nhds hx), hχ] with t hh hp
  refine ⟨hh, hw.1, hw.2.1, hp, fun j => ?_⟩
  rw [Ward.near _ _ _ j.succ_ne_zero]
  exact hw.2.2.2 j

lemma on_shell {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ)
    (y : E4) (hy : y ∈ tsupport (fderiv ℝ χ)) : Points.cons y x ∈ conf _ := by
  have h (i : Fin (n+1)) : x i ∉ tsupport (fderiv ℝ χ) := by
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [notMem_tsupport_iff_eventuallyEq]
      filter_upwards [hw.2.2.1.fderiv (𝕜 := ℝ)] with z hz
      change fderiv ℝ χ z = 0
      simp [hz]
    · exact fun hh => hw.2.2.2 j (tsupport_fderiv_subset ℝ hh)
  have he (i : Fin (n+1)) : y ≠ x i := fun e => h i (e ▸ hy)
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases (fun _ => rfl) (fun j => ?_) j
    simp [Points.cons, he]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [Points.cons, Ne.symm (he i)]
    · simp only [Points.cons, points_apply, Fin.cons_succ]
      exact fun H => congr_arg Fin.succ ((show Injective x.ofLp from hx) H)

lemma cons_cast (x : Points n) (j : Fin n) (b : Axis) (t : ℝ) (y : E4) :
    Points.cons y (Ward.cast x j b t) = Ward.cast (Points.cons y x) j.succ b t := by
  ext1 i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [Ward.cast, Points.cons, Points.direction,
    PiLp.single_apply]
  by_cases h : k = j <;> simp [h]

lemma continuous_cons : Continuous (fun z : E4 × Points n => Points.cons z.1 z.2) :=
  Points.peel.symm.continuous.comp (WithLp.prod_continuous_toLp ..)

variable (h : S.Hierarchy) {W : DiffPlan S} (hd : W.Derivatives S)
include h hd

lemma deriv_cast (x : Points n) (j : Fin n) (b : Axis) (q : Fin n → S.Tag)
    (t : ℝ) (ht : Ward.cast x j b t ∈ conf _) :
    HasDerivAt (fun s => Ward.disc q (Ward.cast x j b s))
      (Ward.disc (update q j (Ward.rise W b (q j))) (Ward.cast x j b t)) t := by
  rw [← Ward.fromD W h hd ht]
  exact ((Ward.cont_disc h q ht).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    (Ward.moves x j b t)

/-- One summand. Justify both operations (derivative of the weight and replacement by the
positional derivative label) on the same fixed shell, moving slot 0 of x and not moving y.
`tsupport (fderiv ℝ χ)` works uniformly in a neighborhood of the parameter. -/
theorem deriv_integral {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (a b : Axis)
    (J : S.Tag) (d : ℕ) (B : S.Field d) (q : Fin n → S.Tag)
    (m m' : ℝ × E4 → ℂ) (cm : Continuous m) (cm' : Continuous m')
    (hm : ∀ (t : ℝ) (y : E4), HasDerivAt (fun s => m (s, y)) (m' (t, y)) t) :
    HasDerivAt (fun t => ∫ y : E4,
      ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m (t, y) *
        S.useAt S (Points.cons y (Ward.cast x 0 b t)) (Fin.cons J (Fin.cons ⟨d, B⟩ q)))
      ((∫ y : E4, ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m' (0, y) *
        S.useAt S (Points.cons y x) (Fin.cons J (Fin.cons ⟨d, B⟩ q))) +
       (∫ y : E4, ((Analysis.D (basis a) χ y : ℝ) : ℂ) * m (0, y) *
        S.useAt S (Points.cons y x) (Fin.cons J (Fin.cons ⟨d+1, W.deriv d b B⟩ q)))) 0 := by
  classical
  obtain ⟨r, hr, hh⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (show {t | Ward.cast x 0 b t ∈ conf _ ∧ Window (Ward.cast x 0 b t) χ} ∈ 𝓝 (0 : ℝ)
      from stable hx hw b)
  let s := closedBall (0 : ℝ) r
  have hs : s ∈ 𝓝 (0 : ℝ) := closedBall_mem_nhds 0 hr
  have zs : (0 : ℝ) ∈ s := mem_of_mem_nhds hs
  let K := tsupport (fderiv ℝ χ)
  have hK : IsCompact K := hw.2.1.fderiv ℝ
  let g (y : E4) : ℂ := ↑(Analysis.D (basis a) χ y)
  have cg : Continuous g := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact Complex.continuous_ofReal.continuousAt.comp
      ((Analysis.dSmooth (hw.1.contDiffAt (x := y)) (basis a) (m := ∞) (by simp)).continuousAt)
  have g_zero (y : E4) (hy : y ∉ K) : g y = 0 := by
    have hf : fderiv ℝ χ y = 0 := image_eq_zero_of_notMem_tsupport hy
    simp [g, Analysis.D, hf]
  let X (t : ℝ) (y : E4) := Points.cons y (Ward.cast x 0 b t)
  let Q : Fin (n+2) → S.Tag := Fin.cons J (Fin.cons ⟨d, B⟩ q)
  let Q' : Fin (n+2) → S.Tag := Fin.cons J (Fin.cons ⟨d+1, W.deriv d b B⟩ q)
  let F (l : ℝ × E4 → ℂ) (w : Fin (n+2) → S.Tag) (t : ℝ) (y : E4) : ℂ :=
    g y * l (t, y) * Ward.disc w (X t y)
  let F' (t : ℝ) (y : E4) := F m' Q t y + F m Q' t y
  have int (l : ℝ × E4 → ℂ) (cl : Continuous l) (w : Fin (n+2) → S.Tag) {t : ℝ} (ht : t ∈ s) :
      Integrable (F l w t) :=
    integrableShell (hh ht).1 (hh ht).2 h.smooth w a (fun y => l (t, y))
      (cl.comp (f := fun y : E4 => (t, y)) (by fun_prop))
  have sep (t : ℝ) (ht : t ∈ s) (y : E4) (hy : y ∈ K) : X t y ∈ conf _ :=
    on_shell (hh ht).1 (hh ht).2 y hy
  have fc (l : ℝ × E4 → ℂ) (cl : Continuous l) (w : Fin (n+2) → S.Tag) :
      ContinuousOn (fun z : ℝ × E4 => F l w z.1 z.2) (s ×ˢ K) := by
    have ht : Continuous (Ward.cast x 0 b) := continuous_iff_continuousAt.mpr
      (fun t => (Ward.moves x 0 b t).continuousAt)
    have cX : Continuous (fun z : ℝ × E4 => X z.1 z.2) :=
      continuous_cons.comp (continuous_snd.prodMk (ht.comp continuous_fst))
    rintro ⟨t, y⟩ ⟨hp, hy⟩
    refine ContinuousAt.continuousWithinAt (s := s ×ˢ K) ?_
    exact (((cg.comp continuous_snd).mul cl).continuousAt).mul
      ((Ward.cont_disc h w (sep t hp y hy)).continuousAt.comp
        (f := fun z : ℝ × E4 => X z.1 z.2) (x := (t, y)) cX.continuousAt)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).prod hK).exists_bound_of_continuousOn
    ((fc m' cm' Q).add (fc m cm Q'))
  let bound := K.indicator fun _ : E4 => C
  have integrable_bound : Integrable bound :=
    (continuousOn_const.integrableOn_compact hK).integrable_indicator hK.measurableSet
  have hB (y : E4) (t : ℝ) (hp : t ∈ s) : ‖F' t y‖ ≤ bound y := by
    by_cases hy : y ∈ K
    · rw [show bound y = C from indicator_of_mem hy _]
      exact hC (t, y) ⟨hp, hy⟩
    · simp [F', F, g_zero y hy, bound, hy]
  have hF (y : E4) (t : ℝ) (ht : t ∈ s) : HasDerivAt (fun u => F m Q u y) (F' t y) t := by
    by_cases hy : y ∈ K
    · have hsep := sep t ht y hy
      have hk : HasDerivAt (fun u => Ward.disc Q (X u y)) (Ward.disc Q' (X t y)) t := by
        let j := (0 : Fin (n+1)).succ
        have he : Q' = update Q j (Ward.rise W b (Q j)) := by
          simp only [Q, Q', j, Fin.cons_succ, Fin.cons_zero, ← Fin.cons_update,
            Fin.update_cons_zero]
          rfl
        simp_rw [X, cons_cast] at hsep ⊢
        rw [he]
        exact deriv_cast h hd _ j b Q t hsep
      exact ((hm t y).const_mul (g y)).mul hk
    · simpa only [F', F, g_zero y hy, zero_mul, add_zero] using! hasDerivAt_const t (0 : ℂ)
  have key : HasDerivAt (fun t => ∫ y : E4, F m Q t y) (∫ y : E4, F' 0 y) 0 :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
      (show ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F m Q t) volume from
        Eventually.mono hs fun t ht => (int m cm Q ht).aestronglyMeasurable)
      (int m cm Q zs)
      (show AEStronglyMeasurable (F' 0) volume from
        ((int m' cm' Q zs).add (int m cm Q' zs)).aestronglyMeasurable)
      (ae_of_all _ hB) integrable_bound (ae_of_all _ hF)).2
  dsimp only [F'] at key
  rw [integral_add (int m' cm' Q zs) (int m cm Q' zs)] at key
  simpa only [F, g, Ward.disc, X, Ward.start, Q, Q'] using key

lemma deriv_shellGrad {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (b i : Axis)
    (J : S.Stress) {d : ℕ} (B : S.Field d) (q : Fin n → S.Tag) :
    HasDerivAt (fun t => shellGrad S J χ i (Ward.cast x 0 b t) q B)
      (shellGrad S J χ i x q (W.deriv d b B)) 0 := by
  unfold shellGrad
  apply HasDerivAt.neg
  apply HasDerivAt.fun_sum
  intro a _
  simpa only [mul_one, mul_zero, zero_mul, integral_zero, zero_add] using
    deriv_integral h hd hx hw a b ⟨4, J a i⟩ d B q (fun _ => 1) (fun _ => 0)
      continuous_const continuous_const (fun t y => hasDerivAt_const t _)

omit h hd

lemma center_eq (v : Ortho.Skew) (c : Axis) (y : E4) (x : Points (n+1)) :
    M4.move v.val (y - x 0) c = M4.move v.val y c - Ward.factor 0 c v x :=
  congr_arg (fun p : E4 => p c) (map_sub (Matrix.toEuclideanLin v.val) y (x 0))

/-- Differentiate the centered angular coefficient: the row is the angular component and
column the motion axis. -/
lemma deriv_center (x : Points (n+1)) (v : Ortho.Skew) (c b : Axis) (y : E4) (t : ℝ) :
    HasDerivAt (fun u => M4.move v.val (y - Ward.cast x 0 b u 0) c) (-(v.val c b)) t := by
  have hk := (Ward.factor (n := n+1) 0 c v).hasFDerivAt.comp_hasDerivAt t
    (Ward.moves x 0 b t)
  rw [Ward.fac, if_pos rfl] at hk
  simp_rw [center_eq]
  simpa only [zero_sub] using! (hasDerivAt_const t (M4.move v.val y c)).sub hk



include h hd

lemma deriv_shellSpin {x : Points (n+1)} (hx : x ∈ conf _) (hw : Window x χ) (b : Axis)
    (J : S.Stress) (v : Ortho.Skew) {d : ℕ} (B : S.Field d) (q : Fin n → S.Tag) :
    HasDerivAt (fun t => shellSpin S J χ v (Ward.cast x 0 b t) q B)
      (shellSpin S J χ v x q (W.deriv d b B) -
        ∑ c : Axis, (v.val c b : ℂ) * shellGrad S J χ c x q B) 0 := by
  let F (a c : Axis) (t : ℝ) := ∫ y : E4,
    ((Analysis.D (basis a) χ y * M4.move v.val (y - Ward.cast x 0 b t 0) c : ℝ) : ℂ) *
      S.useAt S (Points.cons y (Ward.cast x 0 b t)) (Fin.cons ⟨4, J a c⟩ (Fin.cons ⟨d, B⟩ q))
  let A (a c : Axis) := ∫ y : E4,
    ((Analysis.D (basis a) χ y * M4.move v.val (y - x 0) c : ℝ) : ℂ) *
      S.useAt S (Points.cons y x) (Fin.cons ⟨4, J a c⟩ (Fin.cons ⟨d+1, W.deriv d b B⟩ q))
  let L' (a c : Axis) := ∫ y : E4,
    ((Analysis.D (basis a) χ y : ℝ) : ℂ) *
      S.useAt S (Points.cons y x) (Fin.cons ⟨4, J a c⟩ (Fin.cons ⟨d, B⟩ q))
  have row (a c : Axis) : HasDerivAt (F a c) ((-(v.val c b : ℂ)) * L' a c + A a c) 0 := by
    let m (z : ℝ × E4) : ℂ := ↑(M4.move v.val (z.2 - Ward.cast x 0 b z.1 0) c)
    have cm : Continuous m := by
      unfold m
      simp_rw [center_eq]
      have ht : Continuous (Ward.cast x 0 b) := continuous_iff_continuousAt.mpr
        (fun t => (Ward.moves x 0 b t).continuousAt)
      have hc : Continuous (fun y : E4 => M4.move v.val y c) := by
        simp_rw [M4.at_coord]; fun_prop
      exact Complex.continuous_ofReal.comp
        ((hc.comp continuous_snd).sub ((Ward.factor 0 c v).continuous.comp (ht.comp continuous_fst)))
    have hd' : ∀ (t : ℝ) (y : E4), HasDerivAt (fun s => m (s, y)) (-(v.val c b : ℂ)) t := by
      intro t y
      simpa only [m, Complex.ofReal_neg] using (deriv_center x v c b y t).ofReal_comp
    have he := deriv_integral h hd hx hw a b ⟨4, J a c⟩ d B q m (fun _ => -(v.val c b : ℂ))
      cm continuous_const hd'
    simp only [F, L', A, Complex.ofReal_mul]
    simp only [m, Ward.start] at he
    apply he.congr_deriv
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae; filter_upwards with y; ring
  have he := HasDerivAt.fun_sum (u := (Finset.univ : Finset Axis))
    (fun a _ => HasDerivAt.fun_sum (u := (Finset.univ : Finset Axis)) (fun c _ => row a c))
  -- Both shells carry the leading minus sign. Regroup the terms from
  -- differentiating the centering as minus the matrix entries times the translation shells.
  apply (he.neg).congr_deriv
  change -(∑ a : Axis, ∑ c : Axis, (-(v.val c b : ℂ) * L' a c + A a c)) =
    -(∑ a : Axis, ∑ c : Axis, A a c) - ∑ c : Axis, (v.val c b : ℂ) * -(∑ a : Axis, L' a c)
  simp_rw [neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib, mul_neg, Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a c : Axis => (v.val c b : ℂ) * L' a c)]
  rw [Finset.sum_neg_distrib]
  abel

lemma deriv_head {x : Points (n+1)} (hx : x ∈ conf _) (b : Axis) {d : ℕ} (B : S.Field d)
    (q : Fin n → S.Tag) :
    HasDerivAt (fun t => S.useAt S (Ward.cast x 0 b t) (Fin.cons ⟨d, B⟩ q))
      (S.useAt S x (Fin.cons ⟨d+1, W.deriv d b B⟩ q)) 0 := by
  have hh : Ward.cast x 0 b 0 ∈ conf _ := Ward.start x 0 b |>.symm ▸ hx
  have hp := deriv_cast h hd x 0 b (Fin.cons ⟨d, B⟩ q) 0 hh
  simp only [Ward.start, Fin.cons_zero, Fin.update_cons_zero] at hp
  exact hp

omit h hd

theorem answer : YM.Bid.A02 := by
  intro G L S h W hd _ J p Y hw
  -- Test the field identities first with all exterior words. No need here to
  -- use inclusion properties to change caps.
  constructor
  · intro d b v u
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window hx
    have hh : (fun t => shellSpin S J χ v (Ward.cast x 0 b t) q u) =ᶠ[𝓝 0]
        fun t => S.useAt S (Ward.cast x 0 b t) (Fin.cons ⟨d, Y d v u⟩ q) := by
      filter_upwards [stable hx hχ b] with t ht
      exact hw.raw.rotation ht.1 q ht.2 v d u
    have he := (deriv_head h hd hx b (Y d v u) q).unique
      (hh.hasDerivAt_iff.mp (deriv_shellSpin h hd hx hχ b J v u q))
    let T : Fin (n+1) → S.Tag := Fin.cons ⟨d, u⟩ q
    have hf (w : S.Field (d+1)) : S.useAt S x (Fin.cons ⟨d+1, w⟩ q) =
        Ward.here T x 0 (d+1) w := by
      rw [Ward.takes, show T = Fin.cons _ q from rfl, Fin.update_cons_zero]
      rfl
    rw [hf, map_add, map_sum]
    simp_rw [map_smul, smul_eq_mul, ← hf]
    rw [he, hw.raw.rotation hx q hχ v (d+1)]
    simp_rw [hw.raw.translation hx q hχ]
    rw [sub_add_cancel]
  · intro d b i u
    apply S.field_ext h.laws.toSymmetric
    intro n q x hx
    obtain ⟨χ, hχ⟩ := exists_window hx
    have hh : (fun t => shellGrad S J χ i (Ward.cast x 0 b t) q u) =ᶠ[𝓝 0]
        fun t => S.useAt S (Ward.cast x 0 b t) (Fin.cons ⟨d+1, p d i u⟩ q) := by
      filter_upwards [stable hx hχ b] with t ht
      exact hw.raw.translation ht.1 q ht.2 i d u
    have he := (deriv_head h hd hx b (p d i u) q).unique
      (hh.hasDerivAt_iff.mp (deriv_shellGrad h hd hx hχ b i J u q))
    exact he.trans (hw.raw.translation hx q hχ i (d+1) (W.deriv d b u))

end YM.Work.A02
