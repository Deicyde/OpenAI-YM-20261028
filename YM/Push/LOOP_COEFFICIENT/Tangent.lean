import YM.Work.F03.Flat




set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Set Filter MeasureTheory NormedSpace Precision
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators ENNReal InnerProductSpace
variable {G : Gauge}

/-- Left-increment chart from the Lie colors to the (possibly disconnected) image group. -/
def bump (u : G.El) (a : G.Color) := G.lieExp a * u

def delta (u v : G.El) := G.plog (G.mat (v * u⁻¹))

@[simp] lemma bump_zero (u : G.El) : bump u 0 = u := by simp [bump]
@[simp] lemma delta_self (u : G.El) : delta u u = 0 := by simp [delta]

lemma bump_delta (u : G.El) : ∀ᶠ v in 𝓝 u, bump u (delta u v) = v := by
  have hc : Continuous fun v : G.El => v*u⁻¹ := continuous_id.mul continuous_const
  have he := hc.tendsto u; rw [mul_inv_cancel] at he
  filter_upwards [he.eventually G.plog_right] with v hv
  rw [bump,delta,hv,inv_mul_cancel_right]

lemma delta_bump (u : G.El) : ∀ᶠ a in 𝓝 0, delta u (bump u a) = a := by
  simpa only [delta,bump,mul_inv_cancel_right] using G.plog_left

lemma exp_adjoint (u : G.El) (a : G.Color) : G.lieExp (G.adjoint u a) = u * G.lieExp a * u⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_lieExp, G.mat_adjoint, G.mat_mul, G.mat_inv]
  exact G.exp_conjugate _ _

lemma bump_transform (u k h : G.El) (a : G.Color) : bump (k*u*h) (G.adjoint k a) = k*bump u a*h := by
  simp only [bump,exp_adjoint]; group

lemma bump_inverse (u : G.El) (a : G.Color) : bump u⁻¹ (-G.adjoint u⁻¹ a) = (bump u a)⁻¹ := by
  rw [← map_neg, bump,exp_adjoint,Work.F03.exp_neg_color,bump]; group

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x : E} {u v : E → G.El} {a : E → G.Color}

lemma tendsto_mat {X : Type*} {l : Filter X} {f : X → G.El} {v : G.El} :
    Tendsto f l (𝓝 v) ↔ Tendsto (G.mat ∘ f) l (𝓝 (G.mat v)) :=
  (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff

lemma mat_inv_diff (h : ContDiffAt ℝ ω (fun x => G.mat (v x)) x) :
    ContDiffAt ℝ ω (fun x => G.mat (v x)⁻¹) x :=
  (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x h

lemma mat_bump_diff (hu : ContDiffAt ℝ ω (fun x => G.mat (u x)) x)
    (ha : ContDiffAt ℝ ω a x) : ContDiffAt ℝ ω (fun x => G.mat (bump (u x) (a x))) x := by
  simp only [bump, G.mat_mul]; exact (G.exp_jet.contDiffAt.comp x ha).mul hu

lemma delta_diff (hu : ContDiffAt ℝ ω (fun x => G.mat (u x)) x)
    (hv : ContDiffAt ℝ ω (fun x => G.mat (v x)) x) (h : v x = u x) :
    ContDiffAt ℝ ω (fun x => delta (u x) (v x)) x :=
  ContDiffAt.comp (f := fun x => G.mat (v x) * G.mat (u x)⁻¹) x
    (by simpa only [h, ← G.mat_mul, mul_inv_cancel,G.mat_one] using! G.plog_diff)
    (hv.mul (mat_inv_diff hu))

lemma adjoint_diff (hu : ContDiffAt ℝ ω (fun x => G.mat (u x)) x) (ha : ContDiffAt ℝ ω a x) :
    ContDiffAt ℝ ω (fun x => G.adjoint (u x) (a x)) x :=
  G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp (f := fun x =>
    G.mat (u x) * G.colorMat (a x) * G.mat (u x)⁻¹) x
      ((hu.mul (G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp (f := a) x ha)).mul
        (mat_inv_diff hu))

lemma delta_rate {v : ℝ → G.El} {t : ℝ} {a : G.Color}
    (h : HasDerivAt (fun s => G.mat (v s)) (G.colorMat a * G.mat (v t)) t) :
    HasDerivAt (fun s => delta (v t) (v s)) a t := by
  have he := G.expDiff_zero
  have hd := (G.plog_diff.differentiableAt (by simp)).hasFDerivAt
  rw [← show G.mat (G.lieExp 0) = 1 from by simp] at hd
  have H : (fderiv ℝ G.plog 1) (G.colorMat a) = a := by
    have hg := ((hd.comp (g:=G.plog) 0 he).congr_of_eventuallyEq (f₁ := id) (G.plog_left.mono fun _ h => h.symm)
      ).unique (hasFDerivAt_id (𝕜 := ℝ) (0 : G.Color))
    have hx := DFunLike.congr_fun hg a
    simpa only [G.mat_lieExp_zero,G.mat_one] using! hx
  have hh : HasDerivAt (fun s => G.mat (v s * (v t)⁻¹)) (G.colorMat a) t := by
    simpa only [G.mat_mul, Matrix.mul_assoc, G.mat_inv, G.mat_mul_star, mul_one] using!
      h.mul_const (G.mat (v t)⁻¹)
  rw [show G.mat (G.lieExp 0) = G.mat (v t * (v t)⁻¹) by simp] at hd
  rw [← H]
  simpa only [delta, Function.comp_def,mul_inv_cancel,G.mat_one] using! hd.comp_hasDerivAt t hh

lemma exp_price_rate : fderiv ℝ (fun a => G.price (G.lieExp a)) 0 = 0 ∧
    ∀ x y, iteratedFDeriv ℝ 2 (fun a => G.price (G.lieExp a)) 0 ![x,y] = ⟪x,y⟫_ℝ := by
  refine (Work.F03.hessian_of_limit ((Work.F03.price_smooth G.exp_jet.contDiffAt).of_le le_top) ?_
    inner_add_left (fun _ _ => real_inner_comm ..)).2
  intro x; rw [real_inner_self_eq_norm_sq]
  refine Work.F03.price_limit (by simp) ?_
  exact side _ G.expDiff_zero.differentiableAt x |>.congr_deriv (by exact DFunLike.congr_fun G.expDiff_zero.fderiv x)

end

section measure
variable {P : ChartRatio G}

private lemma exp_haar (h : LocalRatio P) {C : Set G.Color} (hC : IsCompact C)
    (hI : C ⊆ Metric.ball 0 P.radius) : G.probHaar (G.lieExp '' C) =
    ∫⁻ a in C, ENNReal.ofReal (P.scale * P.J a) := by
  let B := Metric.ball (0:G.Color) P.radius
  let S := G.lieExp '' C
  have hs : MeasurableSet S := (hC.image G.lieExp_cont).measurableSet
  have he : G.lieExp ⁻¹' S ∩ B = C := by
    refine Subset.antisymm ?_ (fun i hi => ⟨mem_image_of_mem _ hi,hI hi⟩)
    rintro i ⟨⟨j,hj,he⟩,hi⟩; rw [← h.inject (hI hj) hi he]; exact hj
  have hh := congr_arg (fun μ : Measure G.El => μ S) h.actual
  rw [Measure.map_apply G.lieExp_cont.measurable hs, withDensity_apply _ (G.lieExp_cont.measurable hs),
    Measure.restrict_apply hs, inter_eq_left.mpr (image_mono hI),
    Measure.restrict_restrict (G.lieExp_cont.measurable hs), he] at hh
  exact hh.symm

-- compare continuous nonnegative densities at a single point of their common chart
private lemma greater {E : Type*} [MetricSpace E] [MeasureSpace E] [BorelSpace E]
    [IsFiniteMeasureOnCompacts (volume : Measure E)]
    [Measure.IsOpenPosMeasure (volume : Measure E)] [ProperSpace E] {x : E} {U : Set E}
    {F H : E → ℝ} (hs : U ∈ 𝓝 x) (he : ∀ C : Set E, IsCompact C → C ⊆ U →
      (∫⁻ y in C, ENNReal.ofReal (F y)) ≤ ∫⁻ y in C, ENNReal.ofReal (H y))
    (hF : ContinuousAt F x) (hH : ContinuousAt H x) (hp : 0 ≤ H x) : F x ≤ H x := by
  by_contra! hn
  obtain ⟨a,ha,hb⟩ := exists_between hn
  obtain ⟨b,hab,hb'⟩ := exists_between hb
  have hN : ∀ᶠ y in 𝓝 x, y∈U ∧ H y < a ∧ b < F y :=
    (show ∀ᶠ y in 𝓝 x, y∈U from hs).and ((hH.eventually (gt_mem_nhds ha)).and (hF.eventually (lt_mem_nhds hb')))
  obtain ⟨d,hd,h⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hN
  let C := Metric.closedBall x d
  have hu (y : E) (hy : y ∈ C) : y∈U ∧ H y < a ∧ b < F y := h hy
  have hv : IsCompact C := isCompact_closedBall x d
  have hw : 0 < volume C := lt_of_lt_of_le
    (Metric.isOpen_ball.measure_pos volume ⟨x,Metric.mem_ball_self hd⟩) (measure_mono Metric.ball_subset_closedBall)
  refine (he C hv (fun y hy => (hu y hy).1)).not_gt ?_
  calc
    _ ≤ ∫⁻ (_ : E) in C, ENNReal.ofReal a := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.1.le)
    _ < ∫⁻ (_ : E) in C, ENNReal.ofReal b := by
          simp only [lintegral_const, Measure.restrict_apply_univ]
          exact ENNReal.mul_lt_mul_left hw.ne' hv.measure_lt_top.ne
            ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hp.trans ha.le)).mpr hab)
    _ ≤ _ := setLIntegral_mono' hv.measurableSet (fun y hy =>
          ENNReal.ofReal_le_ofReal (hu y hy).2.2.le)

/-- Differential from the given exponential chart to left increments at its image.
The absolute determinant in the physical Lie color basis is the requested
chart density (not its reciprocal). Does not appeal to a normalized path-integral rule. -/
lemma exp_delta_det (h : LocalRatio P) {a : G.Color} (ha : a ∈ Metric.ball 0 P.radius) :
    |(fderiv ℝ (fun x => delta (G.lieExp a) (G.lieExp x)) a).det| = P.J a := by
  let f := fun x => delta (G.lieExp a) (G.lieExp x)
  let J := fun x : G.Color => P.scale * P.J x
  let K := fun x => |(fderiv ℝ f x).det| * J (f x)
  have hf : ContDiffAt ℝ ω f a := delta_diff contDiffAt_const G.exp_jet.contDiffAt rfl
  have hz : f a = 0 := delta_self _
  have h0 := Metric.mem_ball_self (x := (0:G.Color)) h.patch
  have hj : ContinuousAt J a := continuousAt_const.mul (h.germ a ha).continuousAt
  have hc : ContinuousAt K a :=
    ((ContinuousLinearMap.continuous_det.continuousAt.comp (hf.fderiv_right (m:=ω) (by simp)).continuousAt).abs).mul
      (ContinuousAt.comp (f:=f) (g:=J) (continuousAt_const.mul (hz.symm ▸ (h.germ _ h0).continuousAt)) hf.continuousAt)
  let U := {x | x ∈ Metric.ball 0 P.radius ∧ f x ∈ Metric.ball 0 P.radius ∧
    G.lieExp (f x) = G.lieExp x * (G.lieExp a)⁻¹ ∧ DifferentiableAt ℝ f x}
  have hU : U ∈ 𝓝 a := by
    have ht := hf.continuousAt.tendsto; rw [hz] at ht
    filter_upwards [Metric.isOpen_ball.mem_nhds ha, ht.eventually (Metric.ball_mem_nhds _ h.patch),
      (G.lieExp_cont.tendsto a).eventually (bump_delta (G.lieExp a)), hf.eventually (by simp)] with y hy hp hb hh
    change bump _ _ = _ at hb
    exact ⟨hy,hp,by rw [← hb]; simp [bump,f], hh.differentiableAt (by simp)⟩
  have he (C : Set G.Color) (hC : IsCompact C) (hI : C ⊆ U) :
      (∫⁻ x in C, ENNReal.ofReal (J x)) = ∫⁻ x in C, ENNReal.ofReal (K x) := by
    let D := (fun g : G.El => g*(G.lieExp a)⁻¹)
    have hA : G.lieExp '' (f '' C) = D '' (G.lieExp '' C) := by
      apply Subset.antisymm
      · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩; rw [(hI hx).2.2.1]; exact mem_image_of_mem _ (mem_image_of_mem _ hx)
      rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩; rw [← show G.lieExp (f x)=D (G.lieExp x) from (hI hx).2.2.1]; exact mem_image_of_mem _ (mem_image_of_mem _ hx)
    have hi : Injective D := fun _ _ he => mul_right_cancel he
    have hD := measurePreserving_mul_right G.probHaar (G.lieExp a)⁻¹
    have hC' := hC.image_of_continuousOn (f:=f) fun y hy => (hI hy).2.2.2.continuousAt.continuousWithinAt
    have hEq := hD.measure_preimage (hC'.image G.lieExp_cont).measurableSet.nullMeasurableSet
    rw [show D ⁻¹' _ = G.lieExp '' C from hA ▸ hi.preimage_image _, exp_haar h hC (fun y hy => (hI hy).1),
      exp_haar h hC' (by rintro y ⟨x,hx,rfl⟩; exact (hI hx).2.1)] at hEq
    have hIn : InjOn f C := fun i h1 j h2 hij => h.inject (hI h1).1 (hI h2).1
      (mul_right_cancel ((hI h1).2.2.1.symm.trans ((congr_arg _ hij).trans (hI h2).2.2.1)))
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hC.measurableSet
      (fun x hx => (hI hx).2.2.2.hasFDerivAt.hasFDerivWithinAt) hIn] at hEq
    simp only [K, ENNReal.ofReal_mul (abs_nonneg _), J]
    exact hEq
  have hh : J a = K a := le_antisymm (greater hU (fun C hc hs => (he C hc hs).le) hj hc
    (mul_nonneg (abs_nonneg _) (mul_pos h.scale (h.pos _ (hz.symm ▸ h0))).le))
    (greater hU (fun C hc hs => (he C hc hs).symm.le) hc hj (mul_pos h.scale (h.pos _ ha)).le)
  dsimp only [K,J] at hh
  rw [hz,h.anchored,mul_one,mul_comm _ P.scale] at hh
  exact (mul_left_cancel₀ h.scale.ne' hh).symm
end measure
end YM.Push.Loops
