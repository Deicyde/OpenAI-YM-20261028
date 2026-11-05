import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.CoreBudget

/-!
# Budgeting for the W argument tests of the step

Prepare to use the pointwise nonlinear calculation of PhysicalGuard.
Need on these ranks/τ and stencils. `illuminates`: AFTER-L, with books
for stationary log, costs for link, face and transport, a small portion
of Rank tolerance. Uniform in β band. Doesn't include the bias of
CoreBudget or the footprint/PSDs and error rates of Dawn.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle WeightedGaussianMarginal45C.Issue.Cut UVNext.PricedKernels
    YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory
    AnalyticBridge.LocalGaussianLaws Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian FreeResolvent Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

def highPrice (G : Gauge) := (twin_price G).choose
def arcPrice (G : Gauge) := (twin_price G).choose_spec.choose
def pinMargin (G : Gauge) := (twin_price G).choose_spec.choose_spec.choose

def lampRadius (G : Gauge) := (Work.E05.curvature_lower G).choose_spec.choose
def edgeFire (G : Gauge) (x : ℝ) := (arcPrice G + Fintype.card G.ColorIndex)*linkRoom x^2

structure Enlightened (P : Patch) (Pt : Teller G) (w : ℕ) (x β : ℝ) : Prop where
  stable : 0<x
  sparks : 0<β
  plus (C : ℝ) : C = linkRoom x → clearanceFare (retime x) ≤ C ∧ C ≤ pinMargin G ∧ x^(-(7/8):ℝ) ≤ C^2
  books {c f : Side} (S : StepData c f) (T : Tube G S) : S.patch=P → Pt.Funds S T → ∀ F (v : Dir G c), ‖v‖≤ clearanceFare (retime x) →
    ‖doc T F v‖ + Fintype.card G.ColorIndex*x^(-(7/8):ℝ) + coolFraction*phase (betaF G x P.L) ≤ linkRoom x
  low : 4*(highPrice G*linkRoom x) ≤ lampRadius G
  heat : 6*G.colorScale*(highPrice G*linkRoom x)^2 + 4*(edgeFire G x) ≤ phase (betaF G x P.L) / 64
  helm : nautical G (highPrice G*linkRoom x) (coupling β) (w*walls (betaF G x P.L)) + 4*(edgeFire G x/coupling β) + x^(-(1/16):ℝ) ≤ x^(-(1/32):ℝ)

private lemma plate (C : ℝ) {p q : ℝ} (h : p<q) (hv : 0≤C) : ∀ᶠ x : ℝ in atTop, C*x^p ≤ x^q/4 := by
  filter_upwards [const_allow (show 0≤4*C by positivity) h] with x hx
  linarith only [hx]

lemma illuminates (P : Patch) (Pt : Teller G) (w : ℕ) : ∀ᶠ x in atTop, ∀ β : ℝ,x/2 ≤ β → β ≤ 3*x → Enlightened P Pt w x β := by
  obtain ⟨V,hV,H⟩:= carry_summary G P Pt.bind Pt
  obtain ⟨_,p,H'⟩:= (Work.E05.curvature_lower G).choose_spec.choose_spec
  let C:=highPrice G; let N:=(Fintype.card G.ColorIndex:ℝ); let K:=arcPrice G+N
  let D:= 64*(6*G.colorScale*C^2+4*K); have hd:=G.colorScale_pos
  obtain ⟨hC,hK,hp,hA⟩:= (twin_price G).choose_spec.choose_spec.choose_spec; change 0≤C at hC; change 0≤ arcPrice G at hK
  have hk : 0 ≤ K:=add_nonneg hK (Nat.cast_nonneg _)
  have hD : 0 ≤ D:= by unfold D; positivity
  let U:=(8*(w:ℝ)); let z := G.colorScale*(U*C*(4*C)+(U*C+4*C)*(U*C)) + 6*G.colorScale*C^2+4*K; have hz:0 ≤ z:= by unfold z U; positivity
  let t':=(betaF G · P.L)
  have hB := Work.E01.betaF_tendsto G P.L
  have h : ∀ᶠ x in atTop, phase (t' x) ≤ 2*x^(-(1/2:ℝ)+1/16) := by
    filter_upwards [across G P.L, Work.E09.temp_cost (1/16) (by norm_num), hB.eventually phase_fit] with x he hx hp
    exact hp.trans (he.2.2.2.2.1.trans (mul_le_mul_of_nonneg_left hx (by norm_num)))
  have hl : Tendsto (fun x => 4*C*linkRoom x) atTop (𝓝 0) := by simpa using linkRoom_tends.const_mul (4*C)
  have hG := coolFraction_pos
  filter_upwards [eventually_gt_atTop 1, ret_power_scopes 1 zero_le_one,linkRoom_tends.eventually (ge_mem_nhds hp),
    ret_power_scopes (4*V) (by positivity),hl.eventually (ge_mem_nhds p), h, Stock.stepsize (G.slopeConstant * Real.log P.L.val),
    threshold_allows G P.L D hD, band G P.L, band_price G P.L z hz 4,
    plate N (show -(7/8:ℝ) < -(3/8) by norm_num) (Nat.cast_nonneg _),
    plate (coolFraction*2) (show -(1/2:ℝ)+1/16 < -(3/8) by norm_num) (by positivity),
    const_allow (show 0≤(2:ℝ) by norm_num) (show -(1/16:ℝ) < -(1/32) by norm_num)] with x hx hc hr hv h' hh hl hM hβ hh' ht hk' hp'
  intro β hi hi'
  let R:= linkRoom x; let y:= t' x; let B:= w*walls y; let s:= stride 4 x
  have hf : 0 < R := linkRoom_pos (by linarith)
  obtain ⟨he,hg,-⟩ := hβ β hi hi'
  refine ⟨zero_lt_one.trans hx,he,fun u hy=>?_,fun S T he ht' F v hL=> ?_, by linarith only [show 4*C* linkRoom x ≤ lampRadius G from h'],?_,?_⟩
  · subst u
    refine ⟨by simpa using hc,hr,?_⟩; rw [linkRoom_sq (by linarith)]; apply Real.rpow_le_rpow_of_exponent_le hx.le; norm_num
  · apply (add_le_add (add_le_add ((H S T he ht'.knobs ht' F v).trans (mul_le_mul_of_nonneg_left hL hV)) ht) (mul_le_mul_of_nonneg_left hh hG.le)).trans
    have h' : V*clearanceFare (retime x) ≤ linkRoom x/4:= by linarith only [hv]
    change _ + linkRoom x/4 +_ ≤ _; change _ ≤ linkRoom x / 4 at hk'; change 0 < linkRoom x at hf; linarith only [h',hk',hf]
  · unfold edgeFire; change 6*G.colorScale*(C*R)^2+4*(K*R^2)≤_
    change 64*(6*G.colorScale*C^2+4*K)*R^2 ≤ _ at hM; linarith only [hM]
  have hA : 4*(B:ℝ) ≤ U*((1+(radiusB x:ℝ))^2) := by
    change walls y ≤ 2*walls x at hl
    have hy : (walls x:ℝ) ≤ (1+(radiusB x:ℝ))^2 := by
      unfold walls; push_cast; gcongr; change (radiusB x:ℝ) ≤ 1+radiusB x; linarith only
    unfold B U; push_cast; nlinarith only [mul_le_mul_of_nonneg_left (show (walls y:ℝ) ≤ 2*((1+(radiusB x:ℝ))^2) from
      (show (walls y:ℝ) ≤ 2*(walls x:ℝ) by exact_mod_cast hl).trans (mul_le_mul_of_nonneg_left hy (by norm_num))) (Nat.cast_nonneg (α:=ℝ) w)]
  let J:=(1+(radiusB x:ℝ))^2; have hJ : 1≤ J:=one_le_pow₀ (by linarith only [Nat.cast_nonneg (α:=ℝ) (radiusB x)])
  let g:=coupling β; let M:=C*R; let u:=4*(B:ℝ)*M
  have hm : 0≤ M := mul_nonneg hC hf.le
  have hw : u ≤ U*M*J := (mul_le_mul_of_nonneg_right hA hm).trans_eq (by unfold J; ring)
  have hj : G.colorScale*(u*(4*M)+(u+4*M)*u)+6*G.colorScale*M^2+4*(K*R^2) ≤ z*s*R^2 := by
    have hl : J^2=(s:ℝ) := by unfold s J stride; push_cast; ring
    let m:=6*G.colorScale*M^2+4*(K*R^2); have hv : 0 ≤ m := by unfold m; positivity
    have ht : m ≤ m*J^2 := le_mul_of_one_le_right hv (one_le_pow₀ hJ)
    change _ ≤ z*↑s*_
    rw [← hl]; let D:=G.colorScale
    have h2 : 4*M≤ 4*M*J:=le_mul_of_one_le_right (by positivity) hJ
    have hu : u*(4*M)+(u+4*M)*u ≤ (U*M*J)*(4*M*J)+(U*M*J+4*M*J)*(U*M*J) := by
      apply add_le_add (mul_le_mul hw h2 (by positivity) (by positivity)) (mul_le_mul (add_le_add hw h2) hw (by unfold u; positivity) (add_nonneg (by linarith only [show 0≤u from by unfold u; positivity,hw]) (by positivity)))
    simp only [add_assoc]; refine (add_le_add (mul_le_mul_of_nonneg_left hu hd.le) ht).trans_eq ?_
    unfold z m M; ring
  have he' : nautical G M g B+4*(edgeFire G x/g) ≤ x^(-(1/8):ℝ) :=
    le_trans (le_trans (show _ ≤ _ from le_of_eq (show nautical G M g B+4*(edgeFire G x/g)= (G.colorScale*(u*(4*M)+(u+4*M)*u)+6*G.colorScale*M^2+4*(K*R^2))/g from by
      unfold nautical; change _ + 4*(K*R^2/g) = _; dsimp only; unfold u; ring)) (div_le_div_of_nonneg_right hj hg.le)) (hh' _ hi hi')
  apply le_trans (add_le_add (he'.trans (Real.rpow_le_rpow_of_exponent_le hx.le (show -(1/8:ℝ) ≤ -(1/16) by norm_num))) le_rfl)
  linarith only [hp']
end YM.PhysicalNext.InteractingRank
