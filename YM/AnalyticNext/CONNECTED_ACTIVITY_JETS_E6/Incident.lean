import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Compression
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Guide

/-!
# True stroke into the truncated F/I vectors

Uniform affine error through soldered stencils. No
coherent all-field inversion needed. The functions here still take one
U and predictions conditioned on its ACTUAL tags. Use local patches
and broad caps (without variation of V or data from other words).
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.SliceRows
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations Work.E03
open Bloch Laurent Work.F03
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {L : Side} {c f n : Side} {S : StepData c f} {T : Tube G S}

abbrev entryCost (T : Tube G S) (R : ℕ) (U : Config G f) (k : S.Choices) (V : Config G c) : Rod c f → G.Color :=
  Sum.elim (T.Xf R U) (Z S (S.prediction U k) V)

abbrev linearCost (T : Tube G S) (a : LogField G f) (b : LogField G c) : Rod c f → G.Color :=
  Sum.elim (xLin T.high T.up a) (zLin S a b)

theorem entry_turn (hP : P.Funds S T) (R : ℕ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (z : Site c → G.El) (p : Rod c f) :
    entryCost T R (gauge (constantGauge z S.ratio) U) k (gauge z V) p =
      G.adjoint (z (focus S p)) (entryCost T R U k V p) := by
  obtain ⟨_,_,hv,-⟩ := hP.feeds
  rw [← hP.high] at hv
  rcases p with i|b
  · exact DataKernel.plots _ _ hv ..
  dsimp only [entryCost,Sum.elim]
  rw [(Push.SectorMeasure.choice_gauge (Push.SectorMeasure.funds_branch hP) U k _).2,
    show constantGauge z S.ratio ∘ S.ratio.embed = z from funext fun i => congr_arg z (S.ratio.embed_parent i)]
  unfold Z
  rw [map_smul, show gauge z V b * _= z b.1*(V b*(S.prediction U k b)⁻¹)*(z b.1)⁻¹ by unfold Lattice.gauge; group,G.curvature_conjugate]; rfl

lemma entry_stencil {x : ℝ} (hR : Room P S T x) (U W : Config G f) (V X : Config G c) (k : S.Choices) (p : Rod c f) :
    let d := radiusB x/4
    AgreeNear S.ratio.parent (focus S p) d U W → AgreeNear id (focus S p) d V X →
      entryCost T (till x) U k V p=entryCost T (till x) W k X p := by
  intro d hu hv; have he := hR.frame
  rcases p with i|b
  · exact plotted_near _ (Work.E03.parent_step S) _ _ T.high T.up _ _ i le_rfl
      (hu.shrink (by unfold focus; dsimp only; rw [separation_self]; unfold d till; omega))
  dsimp only [entryCost, Sum.elim]
  unfold Z; rw [hv b (by simp [focus]), prediction_near_eq (SectorMeasure.funds_branch hR.accepted) ..]
  apply hu.shrink; simp only [focus,separation_self, zero_add]; unfold d; omega

/-- Global log receipts on bounded extension for both sides. H bounded
sup norms of log fields. -/
theorem entry_near (P : Teller G) (L : Side) {D : Patch} (hd : D.Branches P.bind G)
    {H : ℝ → ℝ} (h : Rate G L (-(1/2)) H) (hp : ∀ᶠ x in atTop, 0 ≤ H x) :
    ∃ M W : ℝ → ℝ, Rate G L (-(1/2)) M ∧ Rate G L (-1) W ∧
      ∀ᶠ x : ℝ in atTop, 0 ≤ M x ∧ 0 ≤ W x ∧ ∀ (c f : Side) (S : StepData c f) (T : Tube G S),
      S.patch = D → P.Funds S T → ∀ (U : LogField G f) (V : LogField G c) (k : S.Choices),
      ‖U‖ ≤ H x → ‖V‖ ≤ H x → ∀ p,
        ‖linearCost T U V p‖ ≤ M x ∧
        ‖entryCost T (till x) (represent U) k (represent V) p - linearCost T U V p‖ ≤ W x := by
  obtain ⟨A,a,hA,ha,hf⟩ := x_chart_cost G P.top 1 (by decide)
  obtain ⟨B,b,hB,hb,hg⟩ := z_chart_cost D P.bind G hd
  let Y x := A*H x
  let F x := B*H x
  let M x := Y x + F x
  let K x := Y x*widen (till x) (H x) P.top.width
  let J x := B*(H x)^2
  let W x := K x+J x
  have hm : Rate G L (-(1/2)) M := (h.mul_left A).add (h.mul_left B)
  have hk : Rate G L (-1) K := by
    convert (h.mul_left A).mul (h.broadens P.top.width_pos hp) using 1; norm_num
  have hj : Rate G L (-1) J := by convert (h.pow 2).mul_left B using 1; norm_num
  refine ⟨M,W,hm,hk.add hj,?_⟩
  filter_upwards [h.below (by norm_num) (min a b) (lt_min ha hb),hp] with x hx hh
  have hl := widen_nonneg (τ:=P.top.width) (till x) hh
  have hm : 0 ≤ Y x := by unfold Y; positivity
  have ht : 0 ≤ F x := by unfold F; positivity
  have he : 0 ≤ K x := mul_nonneg hm hl
  have hs : 0 ≤ J x := mul_nonneg hB.le (sq_nonneg _)
  refine ⟨add_nonneg hm ht, add_nonneg he hs,?_⟩
  intro c f S T hp hg' U V k hu hv p
  obtain ⟨hz,hy⟩ := le_min_iff.mp ((le_abs_self _).trans hx)
  rcases p with i|b
  · obtain ⟨Y₁,V₁,hh,-⟩ := hg'.feeds
    have hh : ‖xLin T.high T.up U i‖ ≤ Y x ∧
        ‖T.Xf (till x) (represent U) i-xLin T.high T.up U i‖ ≤ K x := by
      unfold K Tube.Xf; rw [hg'.high];
      simpa only [Nat.cast_one,div_one] using! hf f T.up Y₁ hh (till x) U (H x) hu hz i
    exact ⟨hh.1.trans (le_add_of_nonneg_right ht),hh.2.trans (le_add_of_nonneg_right hs)⟩
  have hp := hg c f S hp hg'.knobs k b (U,V)
  have Hh : ‖(U,V)‖ ≤ H x := max_le hu hv
  exact ⟨(hp.1.trans (mul_le_mul_of_nonneg_left Hh hB.le)).trans (le_add_of_nonneg_left hm),
    (((hp.2 (Hh.trans hy)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) Hh 2) hB.le)).trans
      (le_add_of_nonneg_left he))⟩

private lemma add_z (S : StepData c f) (p q : LogField G f) (b : LogField G c) (i : Bond c) :
    zLin S (q+p) b i = zLin S q 0 i + zLin S p b i := by
  unfold zLin; rw [← smul_add]; congr 1
  ext j; simp only [PiLp.sub_apply, PiLp.add_apply,Work.F03.parts_add, Matrix.mulVec_add,Pi.add_apply,PiLp.zero_apply,Pi.zero_apply]; abel

lemma linear_add (T : Tube G S) (h : P.Funds S T) (x y : Directions G f) (b : LogField G c) (i : Rod c f) :
    linearCost T (toLog (x+y)) b i=uncutField T x i+linearCost T (toLog y) b i := by
  rcases i with p|i
  · dsimp only [uncutField,linearCost,xLin,Sum.elim]; split
    next hp =>
      obtain ⟨_,_,he,-⟩ := h.feeds; unfold ellLine
      rw [← Summable.tsum_add (ellLine_summable T.up he ..) (ellLine_summable T.up he ..)]
      apply tsum_congr; intro i; simp only [curl_eq,Pi.add_apply,smul_sub,smul_add]; abel
    next hp => simp only [curl_eq,Pi.add_apply,smul_sub,smul_add]; abel
  exact add_z ..

lemma cp_cap (S : StepData c f) (x : LogField G c) : ‖linearCopy S.ratio (collect G x)‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  intro i; unfold linearCopy; split
  next => rw [norm_zero]; exact norm_nonneg _
  exact norm_le_pi_norm x _
end YM.ConnectedActivityE6.SliceRows
