import YM.Bid.Tar
import YM.Org.Twist

/-!
# Germs through each tube using real Lorentz covariance and a boost path

We *consume* `travelable`: in particular, the path property is eventual in
an actual tube near the base point, not just asserted at the base point. We
work with absolute arguments (all of `Full n`). Prove analyticity separately
in the boost parameter (to show agreement) and in those arguments at fixed
boost (for the germs). When complex-boosting the labels, work at a single
finite degree in the same `S.Union`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Work.C19
open Function Set Filter MeasureTheory Distribution Mink Mink.Poincare Boundary
  Boundary.Surface Probe Complex Bid
open scoped Topology ContDiff BigOperators

variable {n : ℕ}

/- Complex-linear maps on Full, including the complex boost at *fixed*
rapidity and the change of names. Careful: `reality` and `shade`
individually are only real-linear. -/

private lemma reality_add (x y : Full n) :
    reality (x + y) = reality x + reality y := by
  apply Points.flatten.injective
  ext i
  simp [reality]

private lemma shade_add (x y : Full n) :
    shade (x + y) = shade x + shade y := by
  apply Points.flatten.injective
  ext i
  simp [shade]

private lemma reality_smul (c : ℂ) (x : Full n) :
    reality (c • x) = c.re • reality x - c.im • shade x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma shade_smul (c : ℂ) (x : Full n) :
    shade (c • x) = c.re • shade x + c.im • reality x := by
  apply Points.flatten.injective
  ext i
  simp [shade, reality]

private lemma glow_ext {x y : Full n} (h : reality x = reality y)
    (k : shade x = shade y) : x = y :=
  (valley x).symm.trans (by rw [h, k, valley])

private def complexMap (A : Points n →ₗ[ℝ] Points n) : Full n →L[ℂ] Full n :=
  LinearMap.toContinuousLinearMap
    { toFun x := glow (A (reality x)) (A (shade x))
      map_add' x y := by
        apply glow_ext <;> simp [reality_add, shade_add]
      map_smul' c x := by
        apply glow_ext <;> simp [reality_smul, shade_smul] }

private def blocks (A : E4 →L[ℝ] E4) : Points n →ₗ[ℝ] Points n where
  toFun x := points fun i => A (x i)
  map_add' x y := PiLp.ext fun i => map_add A (x i) (y i)
  map_smul' c x := PiLp.ext fun i => map_smul A c (x i)

private lemma analytic_name (P : NearPair n) (x : Full n) :
    AnalyticAt ℂ P.name x :=
  (complexMap P.switch.toLinearEquiv.toLinearMap).analyticAt x

private lemma analytic_augment (e : Ray) (z : ℂ) (x : Full n) :
    AnalyticAt ℂ (augment e z) x := by
  let U : Full n →L[ℂ] Full n := ContinuousLinearMap.id ℂ _ +
    Complex.sinh z • complexMap (blocks e.crossT) +
    (Complex.cosh z - 1) • complexMap (blocks e.scalesT)
  have h : augment e z = ⇑U := rfl
  rw [h]
  exact U.analyticAt x

private lemma analytic_boost_path (e : Ray) (x : Full n) (z : ℂ) :
    AnalyticAt ℂ (fun w => augment e w x) z :=
  (analyticAt_const.add (Complex.analyticAt_sinh.smul analyticAt_const)).add
    ((Complex.analyticAt_cosh.sub analyticAt_const).smul analyticAt_const)

/- The change of names must intertwine the action also for the *tilted*
pane. We need this identity only at real rapidities. -/

private lemma augment_real (e : Ray) (t : ℝ) (x : Full n) :
    augment e (↑t) x = rect (e.boost t) x := by
  apply glow_ext
  · simp only [augment, reality_add, reality_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, rect, re_glow]
    ext1 i
    simp [Ray.shift]
  · simp only [augment, shade_add, shade_smul, sinh_ofReal_im, sinh_ofReal_re,
      sub_im, sub_re, cosh_ofReal_im, cosh_ofReal_re, one_re, one_im, sub_zero,
      zero_smul, add_zero, rect, im_glow]
    ext1 i
    simp [Ray.shift]

private lemma name_rect (P : NearPair n) (A : Lorentz) (x : Full n) :
    P.name (rect A x) = rect A (P.name x) := by
  have h (u : Points n) :
      P.switch (togetherL A n u) = togetherL A n (P.switch u) := PiLp.ext fun _ => rfl
  simp only [NearPair.name, rect, re_glow, im_glow, h]

variable {G : Gauge} {L : Register G} {S : Table L} {D : ∀ i, Blanket i}
  {W : Surface S} {X : W.Aurora D} {F : Waves S}

private def emitAt (X : W.Aurora D) (x : Full n) :
    MultilinearMap ℂ (fun _ : Fin n => S.Union) ℂ :=
  let A : Distn (Points n) →ₗ[ℂ] ℂ :=
    { toFun u := ((pref (Points n))⁻¹ : ℂ) * Distn.fourier u (X.lens n x)
      map_add' u v := by simp [mul_add]
      map_smul' c u := by simp [mul_left_comm] }
  A.compMultilinearMap (W.W n)

/- Separate slot labels move holomorphically at a fixed finite degree.
Expand in that finite basis to keep `FullBody.hol`'s fixed-label
hypothesis. In particular no claim about a norm on `Union`. -/
private lemma emit_analytic (hX : X.FullBody F) (d : ℕ) (u : Fin n → ℂ → S.Field d)
    (w : ℂ → Full n) (z : ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) z)
    (hw : AnalyticAt ℂ w z) (hin : w z ∈ tube n) :
    AnalyticAt ℂ (fun b => X.emit (fun i => S.pin d (u i b)) (w b)) z := by
  classical
  let B := Module.finBasis ℂ (S.Field d)
  have he : (fun b => X.emit (fun i => S.pin d (u i b)) (w b)) =
      fun b => ∑ j : Fin n → Fin (Module.finrank ℂ (S.Field d)),
        (∏ i, B.coord (j i) (u i b)) • X.emit (fun i => S.pin d (B (j i))) (w b) := by
    funext b
    have hp : (fun i => S.pin d (u i b)) =
        fun i => ∑ j, B.coord j (u i b) • S.pin d (B j) := by
      funext i
      conv_lhs => rw [← B.sum_repr (u i b), map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul]
      rfl
    rw [hp]
    change emitAt X (w b) _ = _
    rw [MultilinearMap.map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact (emitAt X (w b)).map_smul_univ _ _
  rw [he]
  apply ContDiffAt.analyticAt
  refine ContDiffAt.sum (fun j hj => ?_)
  apply ContDiffAt.mul
  · refine contDiffAt_prod (fun i hi => ?_)
    let A : S.Field d →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (B.coord (j i))
    exact ((A.analyticAt _).comp (hu i)).contDiffAt
  exact ((hX.hol n _ _ hin).comp hw).contDiffAt

/- An anchored germ, also applicable after a change of names `N`. Use
wave_turn for equality on the real boost line (only a neighborhood of zero
is needed), then uniqueness in a *single* complex parameter on the
preconnected path image. `AnalyticOnNhd` gives actual analyticity at each
point of the path, so that image needn't itself be open. -/
private lemma paneAlong {K : Spins S} (hX : X.FullBody F) {R : S.Rotation}
    {h : S.RealSpin} (hK : K.Descends R h) {P : DiffPlan S} (hS : S.Symmetric)
    (hP : P.Inclusions S) (hU : Weighty K) (hTurn : wave_turn F W D X K)
    (v : Fin n → S.Union) (e : Ray)
    (N : Full n → Full n) (hN : AnalyticOnNhd ℂ N univ)
    (hReal : ∀ (a : ℝ) l, N (augment e (↑a) l) = rect (e.boost a) (N l))
    (γ : ℝ → ℂ) (hγ : Continuous γ) (h0 : γ 0 = 0) {x : Full n} {t : ℝ} (ht : 0 ≤ t)
    (hend : N (augment e (γ t) x) ∈ tube n)
    (hpath : ∀ᶠ l in 𝓝[N ⁻¹' tube n] x, ∀ b : ℝ, b ∈ Icc 0 t →
      N (augment e (γ b) l) ∈ tube n) :
    Nonempty (Pane (X.emit v ∘ N) (N ⁻¹' tube n) x) := by
  obtain ⟨d, a, rfl⟩ := P.joint hS hP v
  obtain ⟨U, ha, hr⟩ := hU d e
  let V (z : ℂ) (i : Fin n) := S.pin d (U z (a i))
  let Q (l : Full n) (z : ℂ) := X.emit (V z) (N (augment e z l))
  refine ⟨⟨fun l => Q l (γ t), ?_, ?_⟩⟩
  · exact (hX.hol n (V (γ t)) _ hend).comp (f := N ∘ augment e (γ t))
      ((hN _ (mem_univ _)).comp (f := augment e (γ t)) (analytic_augment e (γ t) x))
  filter_upwards [hpath, self_mem_nhdsWithin] with l hl hin
  let k := X.emit (S.pin d ∘ a) (N l)
  change Q l (γ t) = k
  have ha' : AnalyticOnNhd ℂ (Q l) (γ '' Icc 0 t) := by
    rintro z ⟨b, hb, rfl⟩
    refine emit_analytic hX d (fun i z => U z (a i))
      (fun z => N (augment e z l)) (γ b) (fun i => ?_) ?_ (hl b hb)
    · exact ((ContinuousLinearMap.apply ℂ (S.Field d) (a i)).analyticAt _).comp
        (ha _ (mem_univ _))
    exact (hN _ (mem_univ _)).comp (analytic_boost_path e l _)
  have he (r : ℝ) : Q l (↑r) = k := by
    have hV : V (↑r) = fun i => K.rail (e.boost r) ((S.pin d ∘ a) i) := by
      funext i
      simp only [comp_apply, hK.ties, V, hr]
    change X.emit (V _) (N (augment e _ l)) = _
    rw [hV, hReal]
    exact (hTurn n (S.pin d ∘ a) (e.boost r) (N l) hin).symm
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), Q l z = k := by
    have hu : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · simpa using ((Complex.continuous_ofReal.tendsto 0).mono_left
          (nhdsWithin_le_nhds (s := Ioi 0)))
      filter_upwards [self_mem_nhdsWithin] with r hr
      change (r : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (mem_Ioi.mp hr).ne'
    intro hx
    obtain ⟨r, hr⟩ := (hu.eventually hx).exists
    exact hr (he r)
  have hg : EqOn (Q l) (fun _ => k) (γ '' Icc 0 t) :=
    ha'.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      (isPreconnected_Icc.image γ hγ.continuousOn) ⟨0, left_mem_Icc.mpr ht, h0⟩ hfreq
  exact hg ⟨t, right_mem_Icc.mpr ht, rfl⟩

theorem answer : YM.Bid.C19 := by
  intro G L S K W D F X _hcones hX R h hK P hS hP hU hTurn n v Z y hy ht
  have hg (x : Points n) (hx : x ∈ Z.gap) :
      Nonempty (Pane (X.emit v) (tube n) (glow x (dawn y))) ∧
      Nonempty (Pane ((X.emit (v ∘ Z.s)) ∘ Z.name) (Z.name ⁻¹' tube n) (glow x (dawn y))) := by
    obtain ⟨e, t, hp, ho, hs, hpos, hneg⟩ := ht x hx
    constructor
    · exact paneAlong hX hK hS hP hU hTurn v e id (fun _ _ => analyticAt_id)
        (augment_real e) (fun b => (b : ℂ)*I) (by fun_prop) (by simp) hp.le ho hpos
    exact paneAlong hX hK hS hP hU hTurn (v ∘ Z.s) e Z.name (fun x _ => analytic_name Z x)
      (fun b l => by rw [augment_real, name_rect]) (fun b => -(b : ℂ)*I)
      (by fun_prop) (by simp) hp.le hs hneg
  exact ⟨⟨hy, fun x hx => Classical.choice (hg x hx).1,
    fun x hx => Classical.choice (hg x hx).2⟩⟩

end YM.Work.C19
