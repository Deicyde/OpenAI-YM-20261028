import YM.SectorNext.LARGE_FIELD_REMAINDERS.Marginal


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Earn and pay on that *same* sector

Full-physical multiplicities, no support deletion. Caller elasticity:
mode for orientation, mode for estimating with or without the cut output term,
still permit genuine k-dependent multipliers controlled on the actual region
(points or a.e. on each k's draped slice, not just at minimizing branch). No
large-field a priori assumed. Integrability hypotheses only on multiplier itself.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Remainder
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree MeasureTheory
  Axial YM.Push.SectorMeasure Next.Fluctuations Next.Fluctuations.Sector Scales Metric Oriented Presented
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ENNReal

variable {G : Gauge} {c f n : Side} {S : StepData c f} {x W : ℝ} (d : Allocation G S x W)
  (F : Forest S.ratio) (V : Config G c) (A : Stores S)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Column estimate for arbitrary upstream absolute multiplier invoices. All price
hypotheses besides integrability only on true sector/protected and draped points.
Compared to fixed-volume `floored`, e is an exterior per-coarse-site price, which
we have paid even after β; H and γ here may depend on L. Coarse vision used in
shielded mode. -/
lemma absolute_column {P : Teller G} {T : Tube G S} {C γ e K β : ℝ} (m : Mode) (o : Bool)
    (hT : P.Funds S T) (hβ : y G S.patch.L x / 2 ≤ β) (hx : 0 < y G S.patch.L x) (hγ : 0 < γ)
    (g : S.Choices → F.Slice G → E) (hl : ∀ k, Integrable (g k) (F.order G))
    (h : ∀ k, ∀ᵐ a ∂(F.order G), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k → ‖g k a‖ ≤ K) (hK : 0 ≤ K)
    (hj : ∀ (a : F.Slice G) (k : S.Choices), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k →
      Joint T A (F.drape a) k V x C γ e) :
    let L k a := kernel m o T A x β (F.drape a) k V
    let s := m.size G S.patch.L x
    let sustain := Real.exp (β*e*Fintype.card (Site c))
    let H := K*sustain * outputReserve m o T x β V * hole F A G x s
    (∀ k, Integrable (d.portion A F V (fun k a => L k a • g k a) k) (F.order G) ∧
      ∫ a, ‖d.portion A F V (fun k a => L k a • g k a) k a‖ ∂F.order G ≤ H * room d m F V A C (γ/2) s k) ∧
    ‖d.column A F V (fun k a => L k a • g k a)‖ ≤ H * seats d m F V A C (γ/2) s := by
  intro L s sustain H
  have hs : 0<s := by
    cases m
    · exact Work.E09.temp_pos hx
    exact Scales.gauge _ _ hx
  have hO : 0 ≤ outputReserve m o T x β V := (Real.exp_pos _).le
  let D k := d.portion A F V (fun k a => L k a • g k a) k
  have hb := funds_branch hT
  let u := F.continuous_drape (G:=G) |>.measurable
  have hJ k : Envelope (L k) := by
    have he := env_outgoing hT β x k u (V:=fun _ => V) measurable_const A
    have hw := env_leaves hT A β x k u (V:=fun _ => V) measurable_const
    cases m <;> cases o
    · simpa only [L,clip_single] using he
    · simpa only [L,clip_mean] using hw
    · unfold L; simp only [shield_single]; exact (Envelope.const _).mul he
    unfold L; simp only [shield_mean]; exact (Envelope.const _).mul hw
  have he k : Integrable (D k) (F.order G) :=
    d.portion_integrable hb A F V _ k (Env.smul_L1 (hJ k) (hl k))
  have hy k : ∫ a, ‖D k a‖ ∂F.order G ≤ H * room d m F V A C (γ/2) s k := by
    rw [room, ← integral_const_mul]; apply integral_mono_ae (he k).norm ((room_int d m F V A _ _ _ _ hb).const_mul _)
    filter_upwards [h k] with a ha
    let U := F.drape a; let mass := S.likelihood U k; let inv := d.bill A k U V
    unfold D Allocation.portion
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (d.nonneg ..),Real.norm_of_nonneg (kernel_nonnegative ..)]
    unfold kernel
    change inv*(mass*_ * ‖g k a‖) ≤ H*(inv*(mass*_))
    by_cases ht : inv=0
    · rw [ht]; simp
    by_cases hr : Alive S U k
    swap
    · change ¬Alive S U k at hr; rw [show mass=0 from dead hr]; simp
    let P := sustain * outputReserve m o T x β V
    have hm := joint_light_bound m F V o hβ hx hγ (hj a k ht hr)
    have hg := m.floor_cost (pilot F V) C (γ/2) s hs a (regular A (radiusB x) F)
    rw [show Fintype.card F.Free-(regular A (radiusB x) F).card= (frozen A (radiusB x) F).card from
      (Finset.card_compl _).symm] at hg
    have hP : 0 ≤ P := mul_nonneg (Real.exp_pos _).le hO
    have hw := hm.trans (mul_le_mul_of_nonneg_left hg hP)
    calc
      _ = (inv*mass)*(‖g k a‖*Real.exp _) := by ring
      _ ≤ (inv*mass)*(K * (P * (hole F A G x s * m.lamp (pilot F V) C (γ/2) s a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (ha ht hr) hw (Real.exp_pos _).le hK) (mul_nonneg (d.nonneg ..) hr.le)
      _ = _ := by unfold P H; ring
  refine ⟨fun k => ⟨he k,hy k⟩,?_⟩
  rw [seats,Finset.mul_sum]
  exact (norm_sum_le ..).trans (Finset.sum_le_sum (fun i _ => (norm_integral_le_integral_norm (D i)).trans (hy i)))

/-- Absolute estimates applied to the true single-orientation factors exposed by
sheet_charge. Point invoice, same frontier as `absolute_column`. -/
theorem outgoing_column (m : Mode) {P : Teller G} {T : Tube G S} {C γ e K β : ℝ}
    (hT : P.Funds S T) (hβ : y G S.patch.L x / 2 ≤ β) (hx : 0 < y G S.patch.L x) (hγ : 0 < γ)
    (g : S.Choices → F.Slice G → ℝ) (hl : ∀ k, Integrable (g k) (F.order G))
    (h : ∀ k, ∀ᵐ a ∂(F.order G), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k → ‖g k a‖ ≤ K) (hK : 0 ≤ K)
    (hj : ∀ (a : F.Slice G) (k : S.Choices), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k →
      Joint T A (F.drape a) k V x C γ e) :
    let s := m.size G S.patch.L x
    let sustain := Real.exp (β*e*Fintype.card (Site c))
    let H := K*sustain * outputReserve m false T x β V * hole F A G x s
    let b := match m with | .clipped => (1:ℝ) | .shielded => shield T β x V
    b*d.column A F V (remainder F A T β x V (fun k a => ‖g k a‖)) ≤ H * seats d m F V A C (γ/2) s := by
  intro s sustain H b
  obtain ⟨-,he⟩ := absolute_column d F V A m false hT hβ hx hγ (fun k a => ‖g k a‖) (fun i => (hl i).norm)
    (fun k => by simpa only [norm_norm] using! h k) hK hj
  have hb U k : kernel m false T A x β U k V = b * outgoing A T β x k V U := by
    cases m <;> simp only [b,clip_single,shield_single,one_mul]
  dsimp only at he; simp_rw [hb] at he
  refine (le_trans ?_ (le_trans (le_abs_self _) he))
  apply le_of_eq
  unfold Allocation.column tagTotal Allocation.portion remainder
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with a
  simp only [smul_eq_mul]; ring

/-- Orientation average version for the *actual* leftOver. Still also gives the
option of estimating with the cut sieve pulled out explicit to the final bound. -/
def restBill (R : Rep G f) (T : Tube G S) := d.column A F V (fun k a =>
  ‖exposed R (till x) (F.drape a)‖ * leaves A T R.beta x k V (F.drape a))

lemma rest_estimate (m : Mode) {P : Teller G} {T : Tube G S} {C γ e K σ B Λ δ w : ℝ} {R : Rep G f}
    (hR : R.Lawful σ B Λ δ w) (hT : P.Funds S T) (hβ : y G S.patch.L x / 2 ≤ R.beta) (hx : 0 < y G S.patch.L x) (hγ : 0 < γ)
    (h : ∀ (k : S.Choices), ∀ᵐ a ∂(F.order G), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k →
      ‖exposed R (till x) (F.drape a)‖ ≤ K) (hK : 0 ≤ K)
    (hj : ∀ (a : F.Slice G) (k : S.Choices), d.bill A k (F.drape a) V ≠ 0 → Alive S (F.drape a) k →
      Joint T A (F.drape a) k V x C γ e) :
    let s := m.size G S.patch.L x
    let sustain := Real.exp (R.beta*e*Fintype.card (Site c))
    let H := K*sustain * outputReserve m true T x R.beta V * hole F A G x s
    let b := match m with | .clipped => (1:ℝ) | .shielded => sieve T R.beta x V
    b*restBill d F V A R T ≤ H * seats d m F V A C (γ/2) s := by
  intro s sustain H b
  let g U := ‖exposed R (till x) U‖
  obtain ⟨-,he⟩ := absolute_column d F V A m true hT hβ hx hγ (β:=R.beta) (fun _ a => g (F.drape a))
    (fun _ => ((Env.along (env_exposed R hR (till x)) F.continuous_drape.measurable).integrable _).norm)
    (fun k => by simpa only [g,norm_norm] using! h k) hK hj
  have hb U k : kernel m true T A x R.beta U k V = b * leaves A T R.beta x k V U := by
    cases m <;> simp only [b,clip_mean,shield_mean,one_mul]
  dsimp only at he; simp_rw [hb] at he
  refine (le_trans ?_ (le_trans (le_abs_self _) he))
  apply le_of_eq
  unfold restBill Allocation.column tagTotal Allocation.portion
  rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_const_mul]; apply integral_congr_ae; filter_upwards with a
  simp only [smul_eq_mul,g]; ring
end YM.SectorNext.Remainder
