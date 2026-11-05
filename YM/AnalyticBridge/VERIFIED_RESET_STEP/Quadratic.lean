import YM.AnalyticBridge.VERIFIED_RESET_STEP.Rows

/-! E replacing FDkin and resetting the coefficient of the *clipped* base.
Hard indicators on these quadratic atoms include the kept-row test halo.
Rows kept where an indicator fails still require an attachment, paid on
the true paths; the relaxation rate enters the soft quote. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG UVNext.PricedKernels Next.Scheduling Work.F03 WilsonStartup
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n : Side} {p : BudgetPoint}

def faceCost (G : Gauge) (p : BudgetPoint) :=
    (G.colorScale ^ 2 * 2)⁻¹ * (pairingCost G.Mat p.order * feeWalk G 4 p.power p.order ^ 2)
lemma face_price (o : Site n) (a : PlaqAxes) (p : BudgetPoint) {Z}
    (hz : ∀ U : Config G n,Z U → G.chord (faceValue U (o,a)) ≤ p.threshold) :
    Bill p o Z (faceCost G p*p.threshold^2) fun U : Config G n => G.price (faceValue U (o,a)) := by
  let l := square a.val.1 a.val.2
  have hl : l.length=4 := rfl
  have he := word_fund o l p Z hz
  let c := (G.colorScale^2*2)⁻¹; have h := G.colorScale_pos
  have hC : 0 ≤ c := by dsimp [c]; positivity
  have hp U : G.price (faceValue U (o,a)) = c * inner ℝ (wordStamp o l U) (wordStamp o l U (G:=G)) := by
    rw [real_inner_self_eq_norm_sq]
    have he := G.chord_price (faceValue U (o,a))
    change (‖wordStamp o l U (G:=G)‖ / G.colorScale)^2 = _ at he
    unfold c; field_simp at he ⊢; linarith
  rw [funext hp]; refine Bill.le (Bill.mul_left c (Bill.pair he he)) ?_
  unfold faceCost; rw [abs_of_nonneg hC,hl]; unfold c; apply le_of_eq; ring

lemma slot_line_limit (s : Slot) (o : Site n) (v : Dir G n) :
    Tendsto (fun t : ℝ => t⁻¹ • s.atSite (line v t) o) (𝓝[≠] 0)
      (𝓝 (Exterior.linkSum v (slotFace s o).1 (square s.plaq.val.1 s.plaq.val.2))) := by
  let u : Exterior.fieldDir G n 1 := fun i => v (i.1,Exterior.axisEquiv.symm i.2)
  have he : Exterior.collect G u = v := funext fun i => congrArg (fun j => v (i.1,j)) (Exterior.axisEquiv.left_inv i.2)
  simpa only [Precision.represent, show ∀ t : ℝ, Exterior.collect G (t • u) = t • v from
    fun t => (show Exterior.collect G (t • u) = t • Exterior.collect G u from rfl).trans (congrArg _ he), faceCurl,← Exterior.fundamental,he,slotFace,line] using slot_limit s o u

lemma slot_affine_limit (s : Slot) (o : Site n) (v : LinearJet G) (hx : 10*separation (slotFace s o).1 o < n.val) (hn : 4 ≤ n.val) :
    Tendsto (fun t : ℝ => t⁻¹ • s.atSite (line (v.field o) t) o) (𝓝[≠] 0) (𝓝 (v.positive s.plaq)) := by
  simpa only [Square.cochain_square,v.field_step hx hn,add_sub_cancel_left, LinearJet.curl,LinearJet.positive] using slot_line_limit s o (v.field o)

def rowCost (G : Gauge) (p : BudgetPoint) (l : ℕ) := (2:ℝ)⁻¹ * (pairingCost G.Color p.order * Wages.slotCost G p.power p.order l ^ 2)
def lowCost (G : Gauge) (p : BudgetPoint) (l : ℕ) := (2:ℝ)⁻¹*pairBill G p + (faceCost G p + rowCost G p l)
lemma faceCost_nonneg (G : Gauge) (p : BudgetPoint) : 0 ≤ faceCost G p := by unfold faceCost; have := pairing_nonneg G.Mat p.order; positivity
lemma row_nonneg (G : Gauge) (p : BudgetPoint) (l : ℕ) : 0 ≤ rowCost G p l := by unfold rowCost; have := pairing_nonneg G.Color p.order; positivity
lemma low_nonneg (G : Gauge) (p : BudgetPoint) (l : ℕ) : 0 ≤ lowCost G p l := by
  unfold lowCost; have := pair_nonneg G p; have := faceCost_nonneg G p; have := row_nonneg G p l; positivity

def shapeLoss (p : BudgetPoint) (c : Clip) (G : Gauge) (α Δ : ℝ) (l : ℕ) :=
    (|α+Δ| * (2*p.threshold) + |Δ| * (2:ℝ)⁻¹ * pairBill G p * p.threshold^2) * Real.exp ((l:ℝ)/c.relaxation)

namespace Low
variable (R : PathData G) (c : Clip) (d : Low) (o : Site n)

def fresh (Δ : ℝ) : Pot G n := fun U => (Δ * d.mark R c) * (d.proxy R o U - d.plain R o U)
def maskedPlain (p : BudgetPoint) : Pot G n := masked p.threshold (d.home R p o) fun U => d.mark R c * d.plain R o U

def loan (p : BudgetPoint) (α Δ : ℝ) (U : Config G n) : ℝ := if Healthy p.threshold (d.home R p o) U then 0 else
    (α+Δ)*d.live R c p o U - if Healthy p.threshold {o} U then Δ*d.mark R c*d.proxy R o U else 0

lemma plain_bill (h : Decent c p) : Bill p o (Healthy p.threshold (d.home R p o))
    ((faceCost G p + rowCost G p (d.length R))*p.threshold^2) (d.plain R o) := by
  cases hj : d.2 with
  | inl _ =>
    unfold plain; rw [hj]; simp only [Sum.elim_inl]; refine Bill.le (face_price o d.1 p fun U hU => kept_small _ _ _ _
        (kept_small_halo h (healthy_mono (d.halo_home ..) hU))) ?_
    nlinarith only [mul_nonneg (row_nonneg G p (d.length R)) (sq_nonneg p.threshold)]
  | inr j =>
    let u := d.home R p o
    have hs (s : Slot) (h : s.length ≤ d.length R) (he : Wages.walkCuts s o ⊆ u) :
        Bill p o (Healthy p.threshold u) (Wages.slotCost G p.power p.order (d.length R) * p.threshold) fun U : Config G n => s.atSite U o := by
      have h := Wages.slotPays s s.stencil (Finset.Subset.refl _) _ h o (G:=G) p
      exact ⟨h.smooth, h.nonneg,fun l hl hd U hU => h.bound l hl hd U (healthy_mono he hU)⟩
    obtain ⟨hl,hr⟩ := walk_home R d p o hj
    have he := Bill.mul_left 2⁻¹ (Bill.pair (hs (left R d j) ?_ hl) (hs (right R d j) ?_ hr))
    · unfold plain; rw [hj]; dsimp only [Sum.elim_inr]; simp_rw [div_eq_inv_mul]; refine Bill.le he ?_
      rw [abs_of_pos (by norm_num)]; unfold rowCost
      nlinarith only [mul_nonneg (faceCost_nonneg G p) (sq_nonneg p.threshold)]
    · simp [Low.length,hj]
    simp [Low.length,hj]

lemma proxy_bill (p : BudgetPoint) : Bill p o (Healthy p.threshold {o})
    ((2:ℝ)⁻¹ * (pairBill G p * p.threshold^2)) (proxy R d o) := by
  have h (a b : PlaqAxes) := Bill.mul_left 2⁻¹ (pair_paid (G:=G) p o a b)
  unfold proxy analogue; cases hj : d.2 <;> dsimp only [Sum.elim_inl,Sum.elim_inr] <;>
    simpa only [div_eq_inv_mul,abs_of_pos (show (0:ℝ)<2⁻¹ by norm_num)] using h _ _
lemma fresh_bill (h : Decent c p) (Δ : ℝ) : Bill p o (Healthy p.threshold (d.home R p o))
    (|Δ| * p.threshold^2 * (|d.mark R c| * lowCost G p (d.length R))) (fresh R c d o Δ) := by
  have h' := proxy_bill R d o p
  have hp : Bill p o (Healthy p.threshold (d.home R p o)) ((2:ℝ)⁻¹ * (pairBill G p * p.threshold^2)) (d.proxy R o) :=
    ⟨h'.smooth,h'.nonneg,fun l hl hd U hU => h'.bound l hl hd U (healthy_mono (Finset.singleton_subset_iff.mpr (d.small_home ..)) hU)⟩
  exact Bill.le (Bill.mul_left (Δ * d.mark R c) (Bill.sub hp (d.plain_bill R c o h))) (by rw [abs_mul]; unfold lowCost; apply le_of_eq; ring)
lemma fresh_regular (h : Decent c p) (Δ : ℝ) : p.Regular (d.home R p o) (fresh R c d o Δ) :=
  reg_bill (fresh_bill R c d o h Δ) (continuous_const.mul ((proxy_cont ..).sub (plain_cont ..)) |>.measurable)
    (fun U V hU => by rw [fresh, fresh,d.plain_local R p h.radius o U V hU, d.proxy_local R o U V (agrees_mono hU (Finset.coe_subset.mpr (d.clover_home R h.radius o)))])
    (fun k U => by simp only [fresh, proxy_gauge R d o k U,plain_gauge R d o k U])
@[simp] lemma fresh_one (Δ : ℝ) : d.fresh R c o Δ 1 = 0 := by
  simp [fresh,plain,proxy,analogue,atSite_path,face_one,G.price_one,G.curvature_unit]

lemma plain_limit (h : Nonwrapping (d.home R p o) o) (hn : 4 ≤ n.val) (v : LinearJet G) :
    Tendsto (fun t : ℝ => d.plain R o (line (v.field o) t) / t^2) (𝓝[≠] 0) (𝓝 (d.analogue R v.positive)) := by
  cases hj : d.2 with
  | inl _ =>
    have he : Exterior.linkSum (v.field o) o (square d.1.val.1 d.1.val.2) = v.positive d.1 := by
      rw [Square.cochain_square, v.field_step (h _ (d.small_home R p o)) hn,v.field_step (h _ (d.small_home R p o)) hn]; simp [LinearJet.positive,LinearJet.curl]
    simp only [plain,analogue,hj,Sum.elim_inl,real_inner_self_eq_norm_sq,← he]
    exact price_limit (V:=fun t => faceValue (line (v.field o) t) (o,d.1)) (by simp [face_one]) (Square.word_deriv o _ _)
  | inr j =>
    have hs (s : Slot) (hS : Wages.walkCuts s o ⊆ d.home R p o) := slot_affine_limit s o v (h _ (hS (offset_inside ..))) hn
    have ⟨h',h''⟩ := walk_home R d p o hj
    rw [analogue,hj,Sum.elim_inr]
    exact ((pair_limit (hs _ h') (hs _ h'')).div_const 2).congr (fun t => by simp only [plain,hj,Sum.elim_inr]; ring)
lemma fresh_vanish (hG : G.Simple) (h : Decent c p) (hx : Nonwrapping (d.home R p o) o) (hn : 20 < n.val) (Δ : ℝ) : ∀ x y,
    IsAffineDirection o x → IsAffineDirection o y → logHessian (fresh R c d o Δ) x y = 0 := by
  apply affine_zero (fresh_regular R c d o h Δ); intro v
  have hP : Tendsto (fun t => d.proxy R o (line (v.field o) t) / t^2) (𝓝[≠] 0) (𝓝 (d.analogue R v.positive)) := by
    cases hj : d.2 <;> simp only [proxy,analogue,hj,Sum.elim_inr, Sum.elim_inl] <;>
      exact ((pair_limit (petals_limit _ o hn v) (petals_limit _ o hn v)).div_const 2).congr (fun t => by ring)
  have he := (hP.sub (plain_limit R d o hx (by omega) v)).const_mul (Δ*d.mark R c)
  simp only [sub_self,mul_zero] at he
  simp only [← sub_div,← mul_div_assoc] at he
  have := tendsto_nhds_unique he (hessian_limit hG (d.fresh_regular R c o h Δ) (fresh_one ..) (v.field o)); linarith
lemma visits (p : BudgetPoint) (α Δ U) (he : d.loan R c o p α Δ U ≠ 0) : ¬Healthy p.threshold (d.home R p o) U := fun h => he (if_pos h)
lemma loan_gauge (p : BudgetPoint) (α Δ) : GaugeInvariant (d.loan R c o p α Δ) := by
  intro k U; simp only [loan, Healthy, gauge_flags, live_gauge R c d o k U,proxy_gauge R d o k U]; congr!
lemma loan_meas (p : BudgetPoint) (α Δ) : Measurable (d.loan R c o p α Δ) :=
    Measurable.ite (healthy_closed ..).measurableSet measurable_const <|
      (measurable_const.mul (live_meas ..)).sub (Measurable.ite (healthy_closed ..).measurableSet
        (measurable_const.mul (proxy_cont ..).measurable) measurable_const)
lemma loan_reads (h : Decent c p) (α Δ) : UsesFinal p.threshold (d.home R p o) (d.loan R c o p α Δ) := by
  intro U V he hh
  simp only [loan, healthy_reads _ _ _ (Finset.Subset.refl _) U V he hh, healthy_reads _ {o} _ (Finset.singleton_subset_iff.mpr
    (d.small_home R p o)) U V he hh,d.live_local R c h o U V he, d.proxy_local R o U V (agrees_mono he (Finset.coe_subset.mpr (d.clover_home R h.radius o)))]
lemma loan_bound (p : BudgetPoint) (α Δ U) : ‖d.loan R c o p α Δ U‖ ≤ shapeLoss p c G α Δ (d.length R)* |d.mark R c| := by
  have hp := p.threshold_pos; have hc := c.radius_pos; have hb := pair_nonneg G p
  let e := Real.exp ((d.length R : ℝ)/c.relaxation)
  have he : 1 ≤ e := Real.one_le_exp (by exact div_nonneg (Nat.cast_nonneg _) hc.le)
  have hpos : 0 ≤ shapeLoss p c G α Δ (d.length R) := by unfold shapeLoss; positivity
  unfold loan; split
  · rw [norm_zero]; exact mul_nonneg hpos (abs_nonneg _)
  refine (norm_sub_le ..).trans ?_
  rw [norm_mul,Real.norm_eq_abs]
  let C := (2:ℝ)⁻¹ * pairBill G p * p.threshold^2
  refine (add_le_add (mul_le_mul_of_nonneg_left (d.shapeBound R c o U) (abs_nonneg (α+Δ)))
    (show ‖(if Healthy p.threshold {o} U then Δ*d.mark R c*d.proxy R o U else (0:ℝ))‖ ≤ (|Δ| * |d.mark R c|) * (C*e) from ?_)).trans_eq ?_
  · have hn : 0 ≤ C := by unfold C; positivity
    split
    next h =>
      rw [Real.norm_eq_abs, abs_mul,abs_mul]; gcongr
      exact ((Bill.norm (d.proxy_bill R o p) (l:=[]) (by simp) (by simp) h).trans_eq (by dsimp [C]; ring)).trans
        (le_mul_of_one_le_right hn he)
    rw [norm_zero]; exact mul_nonneg (by positivity) (mul_nonneg hn (zero_le_one.trans he))
  unfold shapeLoss C e; ring
lemma loans_identity (h : Decent c p) (α Δ : ℝ) (U) :
    (α+Δ)*d.live R c p o U + masked p.threshold (d.home R p o) (d.fresh R c o Δ) U =
      α*d.maskedPlain R c o p U + Δ*d.mark R c*masked p.threshold {o} (d.proxy R o) U + d.loan R c o p α Δ U := by
  unfold loan maskedPlain; split
  next he => rw [masked_eq _ _ _ _ he,masked_eq _ _ _ _ he,masked_eq _ _ _ _ (healthy_mono (Finset.singleton_subset_iff.mpr
              (d.small_home ..)) he), live_plain R c d h o he]; unfold fresh; ring
  next he => rw [masked_ne _ _ _ _ he,masked_ne _ _ _ _ he]; split <;> rename_i hb
             · rw [masked_eq _ _ _ _ hb]; ring
             rw [masked_ne _ _ _ _ hb]; ring
lemma loan_sub (p : BudgetPoint) (α Δ α' Δ' U) :
    d.loan R c o p α Δ U - d.loan R c o p α' Δ' U = d.loan R c o p (α-α') (Δ-Δ') U := by
  unfold loan; split_ifs <;> ring
lemma fresh_sub (Δ Δ') : d.fresh R c o Δ - d.fresh R c o Δ' = d.fresh R c o (Δ-Δ') := by funext U; simp [fresh]; ring
end Low
end YM.AnalyticBridge.VerifiedReset
