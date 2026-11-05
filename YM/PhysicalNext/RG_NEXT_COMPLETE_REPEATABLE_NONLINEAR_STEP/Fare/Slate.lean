import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Fare.Sum
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Pane.Limes
import YM.Push.CORRECTED_COLUMNS.Bel

/-! # Seed slack from integral comparison, strict seam tops
 DOES NOT smoothly differentiate fine flags; infer extension from value lower. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Fare
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (F : Forest S.ratio) (T : Tube G S) (k : S.Choices)
    {u v D x s t p a C W : ℝ} {n : ℕ}
section position

lemma faceM (G : Gauge) : ∃ b : ℝ, 0<b ∧ ∀ {c f : Side} {S : StepData c f} (F : Forest S.ratio) (x y : Positions (Joint F G)) (i : Cell f), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
    |toll (Uniform.fine G F x) i-toll (Uniform.fine G F y) i| ≤ b*‖x-y‖ := by
  obtain ⟨Z,he⟩:= paint_supply G 1
  let C:=travelCost G 1 4 (fineCost G 1 Z)
  refine ⟨(1+|C|)/G.colorScale,div_pos (by positivity) G.colorScale_pos,?_⟩; intro c f S F x y i hx hy; let U z:= Uniform.fine G F z; let f₁ z:= faceValue (U z) i; let M z:= G.mat (f₁ z)
  have hk w (hw:w∈closedBall (0:Positions (Joint F G)) 1): Allows 1 M w C:= travel_jets (fun i=> (fine_supply F he).2.2 i w (mem_closedBall_zero_iff.mp hw)) i.1 (show (square _ _).length≤ 4 from (show (square i.2.val.1 i.2.val.2).length≤ 4 by change 4≤ (4:ℕ); norm_num))
  have hp:= (convex_closedBall (0:Positions (Joint F G)) 1).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=M) (C:=C) (fun w hw=> ((hk w hw).analytic).differentiableAt (by simp)) (fun w hw=> by rw [← norm_iteratedFDeriv_one]; exact (hk w hw).norm_le 1 le_rfl) (mem_closedBall_zero_iff.mpr hy) (mem_closedBall_zero_iff.mpr hx)
  apply le_of_mul_le_mul_left _ G.colorScale_pos; rw [← abs_of_pos G.colorScale_pos,← abs_mul,mul_sub,toll,toll,chord_dist,chord_dist,abs_of_pos G.colorScale_pos,← mul_assoc, show G.colorScale*((1+|C|)/G.colorScale)=1+|C| by have ht:= G.colorScale_pos; field_simp]
  apply (abs_norm_sub_norm_le ..).trans; rw [sub_sub_sub_cancel_right]; exact hp.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_add_of_nonneg_left zero_le_one)) (norm_nonneg _))
end position

local notation "Xs" => Positions (Uniform.Primary c G)
local notation "Y" => Poll.Body (Precision.Key F G)
variable (B : BudgetPoint) (β : ℝ) (A : Allocation G S x W) (V : Config G c) (b : Poll.Body (Precision.Key F G))
local notation "R" => Pane.virgin T B β

lemma bare_cost (hc:B.threshold=Pressure.fiery G x S.patch.L) : cutEntry A F T R (Pane.untroubled S) V=output A F β (R).eval (Pane.untroubled S) V := by
  have ht:Fits T R x:= ⟨rfl,rfl,hc⟩
  unfold output cutEntry Allocation.column tagTotal; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; rw [← integral_const_mul]
  apply integral_congr_ae; filter_upwards with a; unfold Allocation.portion SectorMeasure.through; simp only [smul_eq_mul]; rw [show taggedKernel S β k (F.drape a) V*(R).eval (F.drape a) = _ from use_gap ht _ k V]; ring

variable (P : Teller G) (he : Intake P T s (Pane.virgin T B β))
include he
lemma outside_est (hp : 0≤p) (ht : ∀ i, i∉ staying F b (gStep β) D V → overall F T B β V i ≤ p) :
    let Z := ∫ i in (staying F b (gStep β) D V)ᶜ, overall F T B β V i ∂F.order G
    Z ≤ p := by
  intro Z; unfold Z; refine (setIntegral_mono_on ((amt F T B β s P he V).1.integrable _|>.integrableOn) (integrable_const _|>.integrableOn) (staying_meas ..|>.compl) ht).trans ?_
  rw [setIntegral_const, smul_eq_mul]; exact mul_le_of_le_one_left hp measureReal_le_one
lemma coolant (hb : B.threshold=Pressure.fiery G x S.patch.L) {p:ℝ} (hp : 0 ≤ p)
    (ht : ∀ i, i∉ staying F b (gStep β) D V → overall F T B β V i ≤ p) (hs : p<cutEntry A F T R (Pane.untroubled S) V) :
    ∃ y:F.Slice G, y ∈ staying F b (gStep β) D V ∧ ∀ i: Pressure.Cell f,toll (F.drape y) i ≤ B.threshold/2 := by
  by_contra H; push Not at H; rw [bare_cost F T B β A V hb] at hs
  let M:=staying F b (gStep β) D V; let g:=overall F T B β V
  suffices he:output A F β (R).eval (Pane.untroubled S) V ≤ ∫ i in Mᶜ,g i ∂F.order G by exact (not_lt.mpr (he.trans (outside_est F T B β V b P (by assumption) hp ht))) hs
  let q (k:S.Choices) U := A.bill (Pane.untroubled S) k (F.drape U) V * actU F T k B β V U
  have h : S.patch.Branches S.kernel G:= he.ready.knobs.symm ▸ he.ready.kernel
  have hf k : Integrable (q k) (F.order G) := ((A.envelope h F.continuous_drape.measurable measurable_const _ k).mul ((env_tagged _ k h F.continuous_drape.measurable measurable_const).mul (Env.along (Rep.envelope _ he.cap) F.continuous_drape.measurable))).integrable _
  change (∑ k,∫ i,q k i ∂F.order G)≤_
  rw [← integral_finsetSum _ fun k _=> hf k, ← integral_indicator (staying_meas .. |>.compl)]
  apply integral_mono (integrable_finsetSum _ (fun k _=>hf k)) (((amt F T B β s P he V).1.integrable _).indicator (staying_meas ..|>.compl)); intro i
  by_cases hi:i∈M
  · rw [indicator_of_notMem (notMem_compl_iff.mpr hi)]; obtain ⟨j,hj⟩:= H i hi
    refine le_of_eq (sum_eq_zero (fun k _=> ?_))
    have hl : A.bill (Pane.untroubled S) k (F.drape i) V=0:= by
      by_contra hk; have hz:= ((A.actual _ _ _ _ hk).fine j).2 (notMem_empty j); rw [hb] at hj; exact not_lt.mpr hz hj
    unfold q; rw [hl,zero_mul]
  rw [indicator_of_mem hi]; refine sum_le_sum (fun j _=> ?_); apply mul_le_of_le_one_left _ (A.range ..); unfold actU taggedKernel; rw [Pane.sparkling,true_point]; have hx : 0 < prefactor S G β := pow_pos (inv_pos.mpr (S.penaltyZ_pos _)) _; have hh:= S.likelihood_pos (F.drape i) j
  split <;> positivity
end YM.PhysicalNext.Repeat.Fare
