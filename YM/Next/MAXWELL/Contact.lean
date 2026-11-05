import YM.Next.MAXWELL.Regulator

/-!
# Ward charge at the marked leg

Real test of the unrenormalized Maxwell stress. Include the sign from
`soften`: `-∆G₀=δ` normalization. Use only separated contractions on the
LHS (in fact can extend with junk near the marked point without changing
the answer). No assertion of distributional extensions of YM kernels.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace

variable {G : Gauge} {j : ℕ}
variable {U : Set E4} (hU : IsOpen U) (f : Field G.Color) (H : WaveOn U f)
variable (v : Drive) (hv : Killing v)
variable (χ : E4 → ℝ) (hχ : ContDiff ℝ ∞ χ) (Hχ : HasCompactSupport χ) (hs : tsupport χ ⊆ U)
variable {x : E4} (hw : χ =ᶠ[𝓝 x] fun _ => 1)

private def contractedTest (c : G.ColorIndex) (a : Axis) (x : E4) := χ x * (tangent v f a x) c

private lemma test_small (c : G.ColorIndex) (a : Axis) (Hχ : HasCompactSupport χ) :
    HasCompactSupport (contractedTest f v χ c a) := Hχ.mul_right

private lemma tang_component_diff (H : WaveOn U f) (hv : Killing v) {x : E4} (hx : x ∈ U) (c : G.ColorIndex) (a : Axis) :
    ContDiffAt ℝ ∞ (fun z => tangent v f a z c) x :=
  (EuclideanSpace.proj c : G.Color →L[ℝ] ℝ).contDiff.contDiffAt.comp x
    (tangent_diff v f _ hv fun i l => H.smooth i l x hx)

private lemma test_smooth (c : G.ColorIndex) (a : Axis) (H : WaveOn U f) (hv : Killing v)
    (hχ : ContDiff ℝ ∞ χ) (hs : tsupport χ ⊆ U) :
    ContDiff ℝ ∞ (contractedTest f v χ c a) := by
  apply contDiff_iff_contDiffAt.mpr; intro x
  by_cases he : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (tang_component_diff _ _ H hv (hs he) c a)
  refine (contDiffAt_const (c := (0:ℝ))).congr_of_eventuallyEq ?_
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp he] with y hy
  simp [contractedTest, hy]

private lemma skew_test_grad (i l : Axis) (c : G.ColorIndex) (H : WaveOn U f) (hv : Killing v)
    (hs : tsupport χ ⊆ U) (hw : χ =ᶠ[𝓝 x] fun _ => 1) :
    grad i (contractedTest f v χ c l) x - grad l (contractedTest f v χ c i) x = variation v f i l x c := by
  let L := (EuclideanSpace.proj c : G.Color →L[ℝ] ℝ)
  have he (i l) : grad i (contractedTest f v χ c l) x = L (grad i (tangent v f l) x) := by
    rw [← grad_linear L (tangent_diff v f _ hv fun a b => H.smooth _ _ _ (hs (enclosed _ hw)))]
    apply GermD; filter_upwards [hw] with y hy
    simp only [contractedTest,show χ y=1 from hy,one_mul]; rfl
  rw [he,he]; rfl

section Limits
include hU H hv hχ Hχ hs

private theorem pays_reg (i l : Axis) (c : G.ColorIndex) {t : ℝ} (ht : 0 < t) (x : E4) :
    singleFlux v χ (regulated t x i l c) f =
      (∫ y, source t (y-x) * grad l (contractedTest f v χ c i) y) -
        (∫ y, source t (y-x) * grad i (contractedTest f v χ c l) y) := by
  let R := regulated t x i l c
  let F := contractedTest f v χ c
  let P := fun y : E4 => source t (y-x)
  have he (a) := test_smooth f v χ c a H hv hχ hs
  have hk (a) := test_small f v χ c a Hχ
  have hR : ContDiff ℝ ∞ P := ((source_diff ht).comp (f:=fun y => y-x) (contDiff_id.sub contDiff_const)).of_le le_top
  have hp (a b) : Integrable fun y => F a y * grad b P y :=
    cutoff_cost (he a).continuous (hk a) (fun x hx => (gradient_smooth hR b).continuous.continuousAt)
  have hc (a b : Axis) : (∫ y : E4, F a y * grad b P y) = -(∫ y : E4, P y * grad b (F a) y) := by
    rw [show (fun y : E4 => P y * grad b (F a) y) = (fun y => grad b (F a) y * P y) from funext fun y => mul_comm ..]
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (shell_cost (he a) (hk a) (fun y hy => hR.continuous.continuousAt) b) (hp a b)
      (cutoff_cost (he a).continuous (hk a) (fun y hy => hR.continuous.continuousAt))
      (fun x _ => (he a).differentiable (by simp) x) (fun x _ => hR.differentiable (by simp) x)
  have hG := regulated_closed ht x i l c U
  have hw (y : E4) : χ y • (∑ a : Axis, grad a (current v R f a) y) =
      F l y * grad i P y - F i y * grad l P y := by
    by_cases hy : y ∈ tsupport χ
    · have hd (b : Axis) : (∑ d : Axis, (⟪divF R d y,f b d y⟫_ℝ + ⟪R b d y,divF f d y⟫_ℝ)) =
          (f b l y) c * grad i P y - (f b i y) c * grad l P y := by
        have hi (A : G.Color) : ⟪unitColor G c,A⟫_ℝ = A c := by rw [unitColor,EuclideanSpace.inner_single_left]; simp
        have he (d : Axis) : divF f d y = 0 := H.divergence d y (hs hy)
        have hs' (a : Axis) : grad a P y = grad a (source t) (y-x) := shift_gradient ((source_diff ht).contDiffAt.of_le le_top)
        simp_rw [R,he,inner_zero_right, add_zero,regulated_charge ht,
          real_inner_smul_left,hi, sub_mul, Finset.sum_sub_distrib, kr_eq]
        simp [ite_mul,hs',mul_comm]
      rw [current_div hG (wave_closed H) hU hv (hs hy)]
      simp_rw [show regulated t x i l c = R from rfl, hd,F,contractedTest,tangent,
        WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,mul_sub, Finset.sum_sub_distrib,Finset.mul_sum, Finset.sum_mul,
        mul_assoc,mul_sub, Finset.mul_sum]
    simp [image_eq_zero_of_notMem_tsupport hy,F,contractedTest]
  change exportFlux (current v R f) χ = _
  rw [by_parts hχ Hχ fun a y hy => current_diff hv a (fun α β => hG.smooth α β y (hs hy))
    fun α β => H.smooth α β y (hs hy)]
  change (∫ y : E4, χ y • ∑ a : Axis, grad a (current v R f a) y) =
    (∫ y : E4, P y * grad l (F i) y) - (∫ y : E4, P y * grad i (F l) y)
  simp_rw [hw]
  rw [integral_sub (hp ..) (hp ..), hc, hc]
  simp only [sub_neg_eq_add]; ring

omit hU in
private theorem continuous_pays (i l : Axis) (c : G.ColorIndex) (hw : χ =ᶠ[𝓝 x] fun _ => 1) :
    Continuous (fun t : ℝ => singleFlux v χ (regulated t x i l c) f) := by
  unfold singleFlux exportFlux
  refine Continuous.neg (continuous_finsetSum _ fun a _ => ?_)
  let L (z : ℝ × E4) := current v (regulated z.1 x i l c) f a z.2
  let K := tsupport (grad a χ)
  have hk := gradient_small Hχ a
  apply continuousOn_univ.mp (continuousOn_integral_of_compact_support hk ?_ ?_)
  · refine Continuous.continuousOn (continuous_iff_continuousAt.mpr fun z => ?_)
    by_cases he : z.2 ∈ K
    · have hn : x ≠ z.2 := fun hw' => collar hw (hw' ▸ (gradient_part χ a he))
      have hu := hs (tsupport_fderiv_subset ℝ (gradient_part χ a he))
      have hg (b d : Axis) : ContinuousAt (fun y : ℝ × E4 => f b d y.2) z :=
        (H.smooth b d z.2 hu).continuousAt.comp continuousAt_snd
      have hp (b d : Axis) := reg_cont x i l c b d hn
      change ContinuousAt (fun z => grad a χ z.2 * L z) z
      apply ((gradient_smooth hχ a).continuous.comp continuous_snd).continuousAt.mul
      unfold L current cross
      have sum {q : Axis → ℝ × E4 → ℝ} (h : ∀ i ∈ (Finset.univ : Finset Axis), ContinuousAt (q i) z) :
          ContinuousAt (fun p => ∑ i, q i p) z := tendsto_finsetSum _ h
      apply sum; intro b _
      refine ((hv.diff b).continuous.comp continuous_snd).continuousAt.mul (ContinuousAt.sub ?_
        (continuousAt_const.mul ?_))
      · apply sum; intro c _
        exact ((hp a c).inner (hg b c)).add ((hp b c).inner (hg a c))
      apply sum; intro c _; apply sum; intro d _; exact (hp c d).inner (hg c d)
    apply continuousAt_const.congr (g := fun z : ℝ × E4 => grad a χ z.2 * L z)
    filter_upwards [continuousAt_snd.preimage_mem_nhds ((isClosed_tsupport (grad a χ)).isOpen_compl.mem_nhds he)] with y hy
    change 0 = grad a χ y.2 * L y
    rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  intro t x _ hx; simp only [image_eq_zero_of_notMem_tsupport hx, zero_smul]

include hw

/-- Local stress with the source connected once. The sign includes all
choices: Green, curl at both ends, outward flux and stress as in `cross`. -/
theorem local_force (i l : Axis) (c : G.ColorIndex) :
    singleFlux v χ (pulse (omegaLeg c i l) x) f = - variation v f i l x c := by
  have ht : singleFlux v χ (pulse (omegaLeg c i l) x) f =
      singleFlux v χ (regulated 0 x i l c) f := by
    unfold singleFlux exportFlux; congr 1; apply Finset.sum_congr rfl; intro a _
    apply integral_congr_ae; refine Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport (grad a χ)
    · have hs : x ≠ y := fun h => collar hw (h ▸ gradient_part χ a hy)
      simp_rw [current,cross,reg_pulse hs]
    simp [image_eq_zero_of_notMem_tsupport hy]
  rw [ht]
  refine tendsto_nhds_unique ((continuous_pays f H v hv χ hχ Hχ hs i l c hw).continuousAt.continuousWithinAt
    (x := (0:ℝ)) (s := Ioi 0)) ?_
  let F := contractedTest f v χ c
  have he (a b : Axis) := testing_source (gradient_smooth (test_smooth f v χ c a H hv hχ hs) b).continuous
    (gradient_small (test_small f v χ c a Hχ) b) x
  rw [← skew_test_grad f v χ i l c H hv hs hw, neg_sub]
  refine ( (he i l).sub (he l i) ).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (pays_reg hU f H v hv χ hχ Hχ hs i l c ht x).symm
end Limits
end YM.Maxwell.Free
