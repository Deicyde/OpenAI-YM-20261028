import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.LocalH.Chart
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Broad
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Ratio
import YM.Work.A15
import YM.Work.B06


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Sharpen Haar ratio overhead to 1 on any certified chart

Needed if extracting the gain on a packet without yet charging *all*
chart bills.  uses a contraction property. Here derive for
`G.Color` (compact matrix group, given normalized real Lie coordinates)
by dividing the rotation in two repeatedly. Then compare arbitrary J
using shifted compact tests. No connectedness or simple input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Lattice RG Wilson Precision Exterior Tree MeasureTheory Metric Matrix  NormedSpace Set
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius ENNReal
open LocalH
variable {G : Gauge}

private def walk (u : G.El) (x : G.Color) := u*G.lieExp x

private lemma move_smooth (x : G.Color) : ContDiffAt ℝ ω (move G (G.lieExp x)⁻¹) x := by
  unfold move snap
  let y := (G.lieExp x)⁻¹
  have he : ContDiff ℝ ω (fun b : G.Color => G.mat (y*G.lieExp b)) := by
    simp only [G.mat_mul]; exact contDiff_const.mul G.exp_jet
  have hp : ContDiffAt ℝ ω G.plog (G.mat (y * G.lieExp x)) := by simpa [y] using G.plog_diff
  exact hp.comp (f:=fun b => G.mat (y*G.lieExp b)) x he.contDiffAt

private lemma complete_coat (x : G.Color) :
    HasFDerivAt (fun a => G.mat (walk (G.lieExp x)⁻¹ a))
      (G.colorMat.toContinuousLinearMap.comp (coat G x)) x := by
  let y := (G.lieExp x)⁻¹
  let F := move G y
  have hs : F x=0 := by simp [F,move,snap,y]
  have he : HasFDerivAt F (coat G x) x := ((move_smooth _).differentiableAt (by simp)).hasFDerivAt
  have hh := G.expDiff_zero; rw [← hs] at hh
  apply (hh.comp x he).congr_of_eventuallyEq
  have ht : Tendsto (walk y) (𝓝 x) (𝓝 1) := by
    have ht := (show Continuous (walk y) by unfold walk; exact continuous_const.mul G.lieExp_cont).tendsto x
    simpa only [walk,y, inv_mul_cancel] using ht
  filter_upwards [ht.eventually G.plog_right] with v hv
  exact congr_arg G.mat hv.symm

private def halfCoat (y : G.El) : G.Color →ₗ[ℝ] G.Color := (1/2 : ℝ) • (LinearMap.id + G.adjoint y)

lemma divided_coat (x : G.Color) :
    let b := (1/2:ℝ) • x; let y := (G.lieExp b)⁻¹
    (coat G x).toLinearMap=(halfCoat y).comp (coat G b).toLinearMap := by
  intro b y
  have n (v : G.Color) : G.lieExp v=G.lieExp ((1/2:ℝ) • v)*G.lieExp ((1/2:ℝ) • v) := by
    apply G.mat_injective
    rw [G.mat_mul]
    letI : NormedAlgebra ℚ G.Mat := .restrictScalars ℚ ℝ _
    simp only [G.mat_lieExp,map_smul]
    let u : G.Mat := (1/2 : ℝ) • G.colorMat v
    have hi : exp (u+u)=exp u * exp u := exp_add_of_commute (Commute.refl u)
    rw [← hi]
    unfold u; rw [← add_smul]
    norm_num
  apply LinearMap.ext
  intro z
  let Q (t : ℝ) := x+t • z
  let P (t : ℝ) := b+t • ((1/2:ℝ) • z)
  have he (t) : P t=(1/2:ℝ) • Q t := by unfold P Q b; module
  have hz : P 0=b := by simp [P]
  have hw : Q 0=x := by simp [Q]
  let B (t) := walk y (P t)
  let A (t) := walk (G.lieExp x)⁻¹ (Q t)
  have hb : B 0=1 := by unfold B walk; rw [hz]; exact inv_mul_cancel _
  have hh (t : ℝ) : A t=(y*B t*y⁻¹)*B t := by
    unfold A B walk y
    nth_rw 1 [n x]
    nth_rw 1 [n (Q t)]
    rw [he]
    unfold b; group
  let u := G.colorMat (coat G x z); let v := G.colorMat (coat G b ((1/2:ℝ) • z))
  have hu : HasDerivAt (fun t => G.mat (A t)) u 0 := by
    have hx : HasDerivAt Q z 0 := by simpa [Q] using! ((hasDerivAt_id' (0:ℝ)).smul_const z).const_add x
    have he := complete_coat x -- comp with Q, y held fixed
    have hd : HasFDerivAt (fun a => G.mat (walk (G.lieExp x)⁻¹ a))
      (G.colorMat.toContinuousLinearMap.comp (coat G x)) (Q 0) := hw.symm ▸ he
    exact hd.comp_hasDerivAt 0 hx
  have hv : HasDerivAt (fun t => G.mat (B t)) v 0 := by
    have hx : HasDerivAt P ((1/2:ℝ) • z) 0 := by
      simpa [P] using! ((hasDerivAt_id' (0:ℝ)).smul_const ((1/2:ℝ) • z)).const_add b
    have hd : HasFDerivAt (fun a => G.mat (walk (G.lieExp b)⁻¹ a))
      (G.colorMat.toContinuousLinearMap.comp (coat G b)) (P 0) := hz.symm ▸ complete_coat b
    exact hd.comp_hasDerivAt 0 hx
  simp_rw [hh,G.mat_mul,G.mat_inv] at hu
  set Y := G.mat y
  have h1 := hu.unique (((hv.const_mul Y).mul_const (star Y)).mul hv)
  rw [hb,G.mat_one] at h1
  apply G.colorMat_injective
  change u = G.colorMat ((halfCoat y) (coat G b z))
  rw [h1, mul_one, mul_one,show Y*star Y=1 from G.mat_mul_star _, one_mul]
  unfold v halfCoat
  set w := coat G b z
  simp only [LinearMap.comp_apply, LinearMap.smul_apply,LinearMap.add_apply,LinearMap.id_coe, id_eq, map_smul,
    map_add, G.mat_adjoint, Gauge.conjugate, mul_smul_comm, smul_mul_assoc,smul_add, Y]
  exact add_comm ..

private lemma det_cost (Y : G.El) : |LinearMap.det (halfCoat Y)| ≤ 1 := by
  let L := (halfCoat Y).toContinuousLinearMap
  have H (x : G.Color) : ‖L x‖ ≤ ‖x‖ := by
    change ‖(1/2:ℝ) • (x+G.adjoint Y x)‖ ≤ _
    rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤1/2)]
    have he := norm_add_le x (G.adjoint Y x)
    rw [G.norm_adjoint] at he; linarith
  let X := closedBall (0:G.Color) 1
  have hx : L '' X ⊆ X := by
    rintro _ ⟨x,hx,rfl⟩; change L x ∈ closedBall 0 1; simp only [mem_closedBall,dist_zero_right]; exact (H _).trans (by simpa [X] using hx)
  let μ : Measure G.Color := volume
  have hl := measure_mono hx (μ:=μ)
  rw [μ.addHaar_image_continuousLinearMap] at hl
  have ht := isCompact_closedBall (0:G.Color) (1:ℝ)
  have hp : 0 < μ X := lt_of_lt_of_le (isOpen_ball.measure_pos μ ⟨0,mem_ball_self (by norm_num : (0:ℝ)<1)⟩) (measure_mono ball_subset_closedBall)
  have hs := ht.measure_lt_top (μ:=μ)
  refine (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 1)).mp ?_
  rw [ENNReal.ofReal_one]
  apply (ENNReal.mul_le_mul_iff_left hp.ne' hs.ne).mp
  rwa [one_mul]

/-- Canonical Haar ratio at any log point costs at most one. -/
theorem spinning (x : G.Color) : |spin G x| ≤ 1 := by
  let F := fun x : G.Color => |spin G x|
  let d : ℝ := 1/2
  have he (x : G.Color) : F x ≤ F (d • x) := by
    unfold F spin
    change |LinearMap.det (coat G x).toLinearMap| ≤ |LinearMap.det (coat G _).toLinearMap|
    rw [divided_coat x,LinearMap.det_comp,abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (det_cost _)
  have ht (i : ℕ) : F x ≤ F (d^i • x) := by
    induction i with
    | zero => simp
    | succ i ih => exact ih.trans (by simpa only [smul_smul,pow_succ',Nat.succ_eq_add_one] using he (d^i • x))
  have hp : ContinuousAt F 0 := (spin_deriv G 0).continuousAt.abs
  have hm := ((tendsto_pow_atTop_nhds_zero_of_lt_one (show 0 ≤ d by unfold d; norm_num) (show d < 1 by unfold d; norm_num)).smul_const x)
  rw [zero_smul] at hm; have hh := hp.tendsto.comp hm
  have hh' : Tendsto (fun i : ℕ => F (d^i • x)) atTop (𝓝 1) := by
    simpa only [Function.comp_apply,zero_smul,F,spin_zero,abs_one] using! hh
  exact ge_of_tendsto hh' (Eventually.of_forall ht)
/-- Identify the committed J at *every* priceable point by moving a
compact test back to origin (translation on group, plog at origin only).
In particular can't assume an arbitrary positive analytic density on
the link chart with correct scale but wrong center curvature. -/
lemma contracted {Z : ChartRatio G} (h : LocalRatio Z) {x : G.Color} (hx : x∈ball 0 Z.radius) :
    Z.J x = |LocalH.spin G x| := by
  let u := G.lieExp x
  let P := move G u⁻¹
  let B := ball (0:G.Color) Z.radius
  let R (y : G.Color) := Z.scale * Z.J y
  let F (y : G.Color) := |(fderiv ℝ P y).det| *R (P y)
  let s : Set G.Color := {y | y∈B ∧ P y∈B ∧ u*G.lieExp (P y)=G.lieExp y ∧ ContDiffAt ℝ ω P y}
  have hp : P x=0 := by simp [P,move,u,snap]
  have hD := move_smooth x
  have ht : ContinuousAt P x := hD.continuousAt
  have H := ht.tendsto; rw [hp] at H
  let t := fun v => u⁻¹*G.lieExp v
  have hh := (show Continuous t from continuous_const.mul G.lieExp_cont).continuousAt (x:=x)
  have hs : s∈𝓝 x := by
    have he := hh.tendsto
    rw [show t x=1 from inv_mul_cancel _] at he
    filter_upwards [isOpen_ball.mem_nhds (s:=B) hx, H (isOpen_ball.mem_nhds (mem_ball_self h.patch)), he.eventually G.plog_right,
      hD.eventually (by simp)] with y h1 h2 h3 h4
    refine ⟨h1,h2,?_,h4⟩
    change u * G.lieExp (LocalH.snap G (t y))=_
    change G.lieExp (LocalH.snap G (t y))=t y at h3
    rw [h3]; unfold t; group
  have hR : ContinuousAt R x := continuousAt_const.mul (h.germ x hx).continuousAt
  have hF : ContinuousAt F x := by
    have hi : ContinuousAt (fun y => |(fderiv ℝ P y).det|) x :=
      (ContinuousLinearMap.continuous_det.continuousAt.comp (hD.fderiv_right (m:=ω) (by simp)).continuousAt).abs
    have hm : ContinuousAt R (P x) := hp.symm ▸ continuousAt_const.mul (h.germ _ (mem_ball_self h.patch)).continuousAt
    exact hi.mul (hm.comp ht)
  have hr (z : G.Color) (hz : z∈B) : 0 ≤ R z := (mul_pos h.scale (h.pos _ hz)).le
  have hb (c : Set G.Color) (hc : IsCompact c) (he : c ⊆ s) :
      (∫⁻ y in c, ENNReal.ofReal (R y)) = ∫⁻ y in c, ENNReal.ofReal (F y) := by
    have h0 : ∀ y∈c,y∈B ∧ P y∈B ∧ u*G.lieExp (P y)=G.lieExp y ∧ ContDiffAt ℝ ω P y := fun _ hy => he hy
    have ha : ContinuousOn P c := fun y hy => (h0 y hy).2.2.2.continuousAt.continuousWithinAt
    have hi : InjOn P c := by
      intro i hi j hj hh
      exact h.inject ((h0 _ hi).1) ((h0 _ hj).1) (((h0 _ hi).2.2.1).symm.trans ((congr_arg (fun z => u*G.lieExp z) hh).trans ((h0 _ hj).2.2.1)))
    have hQ : G.lieExp '' (P '' c) = (fun v => u*v) ⁻¹' (G.lieExp '' c) := by
      ext y; constructor
      · rintro ⟨_,⟨z,hz,rfl⟩,rfl⟩
        exact ⟨z,hz,(h0 z hz).2.2.1.symm⟩
      rintro ⟨z,hz,hz'⟩
      exact ⟨P z,⟨z,hz,rfl⟩,mul_left_cancel (((h0 z hz).2.2.1).trans hz')⟩
    have hd : G.probHaar (G.lieExp '' c)=G.probHaar (G.lieExp '' (P '' c)) := by
      rw [hQ,(measurePreserving_mul_left G.probHaar u).measure_preimage (hc.image G.lieExp_cont).measurableSet.nullMeasurableSet]
    have hM : P '' c ⊆ B := by rintro _ ⟨y,hy,rfl⟩; exact (h0 _ hy).2.1
    rw [cap_price h c hc (fun i hi => (h0 i hi).1), cap_price h _ (hc.image_of_continuousOn ha) hM] at hd
    rw [hd,lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hc.measurableSet (f':=fun y => fderiv ℝ P y) _ hi]
    · unfold F
      simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]; rfl
    intro y hy; exact ((h0 y hy).2.2.2.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hE := hr x hx
  have hH : 0 ≤ F x := mul_nonneg (abs_nonneg _) (hp.symm ▸ hr 0 (mem_ball_self h.patch))
  have hQ : R x=F x := le_antisymm (price_le_of_caps hs hF hR hH (fun t ht hs => (hb _ ht hs).symm))
    (price_le_of_caps hs hR hF hE hb)
  unfold R F at hQ; rw [hp] at hQ; unfold R at hQ; rw [h.anchored,mul_one,mul_comm Z.scale] at hQ
  exact mul_right_cancel₀ h.scale.ne' hQ

theorem gentle_ratio {Z : ChartRatio G} (h : LocalRatio Z) {x : G.Color} (hx : x∈ball 0 Z.radius) :
    0 < Z.J x ∧ Z.J x ≤ 1 := ⟨h.pos x hx, by rw [contracted h hx]; exact spinning _⟩

theorem gentle_extended {Z : ChartRatio G} (h : LocalRatio Z) (q : Push.SectorMeasure.Chi)
    {d : ℝ} (hd : 0<d) (ht : 4*d<Z.radius) (x : G.Color) : 0 < extended q Z d x ∧ extended q Z d x ≤ 1 := by
  refine ⟨extended_pos .., Real.exp_le_one_iff.mpr ?_⟩
  unfold logGuard
  by_cases hi : ‖x‖ < Z.radius
  · obtain ⟨h1,h2⟩ := gentle_ratio h (x:=x) (by simpa using hi)
    exact mul_nonpos_of_nonneg_of_nonpos (broad_range q x _).1 (Real.log_nonpos h1.le h2)
  rw [show broad q (2*d) x = 0 from ?_,zero_mul]
  by_contra he; have hh := broad_span q (d:=2*d) (by linarith) _ he; linarith
end YM.Next.SectorChange
