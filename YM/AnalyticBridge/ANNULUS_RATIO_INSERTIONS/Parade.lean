import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Echo

/-!
# Common purchase for some Gaussian uses *with* the compulsory invoice

Supports exact ratio contacts at their order-zero inlet prescriptions,
and arbitrary explicitly charged score companions (no score V producers
here). Trigger weights with post-delay geometry-polynomial reserve at
hat scale. Counts even a linked score reading all z. Local price, not a
normalized remainder/gas estimate. Before averaging output, even when
likelihood tags/flags in sector.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.Parade
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented Presented LabelSum
open Tier Wisps Schur LocalJet Completion
open SectorNext.Remainder SectorNext.Remainder.Affine Harvest Dress
open  Prism Prism.Breeze Prism.Arc 
open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

/-- Physical threshold t/g times the post-L convention constant. -/
def anxious (G : Gauge) (N : Side) (x θ β : ℝ) := θ * (fiery G x N / coupling β)
lemma anxiety (G : Gauge) (N : Side) (x θ β : ℝ) (h : 0≤θ) (hy : 0<Scales.y G N x)
    (hb : Scales.y G N x /2 ≤ β) : θ/2*Scales.p G N x ≤ anxious G N x θ β := by
  unfold anxious; rw [Scales.fi,coupling,div_inv_eq_mul]
  set y := Scales.y G N x
  have hl : 0 < β := (half_pos hy).trans_le hb
  have ht : Real.sqrt β ≥ Real.sqrt y/2 := by
    have he := Real.sqrt_le_sqrt hb
    have hs : Real.sqrt (y/2) = Real.sqrt y / Real.sqrt 2 := Real.sqrt_div hy.le _
    rw [hs] at he; apply le_trans _ he
    have hj := Real.sq_sqrt (show 0≤(2:ℝ) by norm_num)
    have hh : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
    have hζ := Real.sqrt_pos.2 (show 0<(2:ℝ) by norm_num)
    rw [le_div_iff₀ hζ]
    nlinarith [mul_pos hh hζ]
  apply le_trans (b:=θ * (Scales.g G N x * Scales.p G N x * (Real.sqrt y/2))) ?_
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (mul_nonneg (Scales.gauge G N hy).le (Scales.pos G N x).le)) h)
  refine le_of_eq ?_
  have he : Scales.g G N x * Real.sqrt y = 1 := inv_mul_cancel₀ (Real.sqrt_pos.2 hy).ne'
  calc
    _ = θ/2*Scales.p G N x*(Scales.g G N x*Real.sqrt y) := by rw [he,mul_one]
    _ = _ := by ring

def rateTrigger (L θ : ℝ) := pinch L * (θ/2)^2/2
lemma rateTrigger_pos (L θ : ℝ) (hL : 0<L) (hθ : 0<θ) : 0<rateTrigger L θ := by unfold rateTrigger; have := pinch_pos hL; positivity

/-- even with any fixed poly-bill at each distinct trigger
(support weighted hit still needed). This is one all-info trigger-noise
quote, not promising the pressure scales against an arbitrary threshold
selected after delay. d_/cover in this sampler not addressed. -/
lemma fires (G : Gauge) (N : Side) (L θ E : ℝ) (n : ℕ) (hE : 0≤E) (hL : 0<L) (hθ : 0<θ) :
    ∀ᶠ x:ℝ in atTop, ∀ β : ℝ, Scales.y G N x /2 ≤ β → 0≤anxious G N x θ β ∧ ∀ m : ℕ,
      Arc.tail L (anxious G N x θ β) m*tuck G^m * (E*(Scales.b x)^n)^m ≤
        Real.exp (-rateTrigger L θ * Scales.p G N x^2*m) := by
  let t := pinch L
  have ht : 0<t:=pinch_pos hL
  let v:=rateTrigger L θ
  have hv : 0<v:=rateTrigger_pos _ _ hL hθ
  have hx : Tendsto (fun x:ℝ=>tuck G*E*((Scales.b x)^n/(Scales.p G N x)^2)) atTop (𝓝 0) := by
    simpa only [mul_zero, Real.rpow_two] using ((Scales.cover_pay G N n (a:=(2:ℝ)) (by norm_num)).const_mul (tuck G*E))
  filter_upwards [hx.eventually (ge_mem_nhds hv),(Scales.year G N).eventually_gt_atTop 0] with x hx hy
  intro β hβ
  let y:=Scales.p G N x; let R:=anxious G N x θ β
  have hp : 0<y := Scales.pos ..
  have he := anxiety G N x θ β hθ.le hy hβ
  change θ/2*y ≤ R at he
  have hN : 0≤R := by nlinarith
  refine ⟨hN,fun m=>?_⟩
  rw [mul_div_assoc' (tuck G*E)] at hx -- direction?
  have hF : tuck G*E*Scales.b x ^ n ≤ v*y^2 := (div_le_iff₀ (by positivity)).mp hx
  have hb : tuck G^m*(E*Scales.b x^n)^m ≤ Real.exp (v*y^2*m) := by
    rw [← mul_pow, ← mul_assoc, mul_comm (v*y^2), Real.exp_nat_mul]
    refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg (tuck_pos G).le hE) (pow_nonneg (zero_le_one.trans (Scales.size x)) _)) ?_ _
    linarith only [hF,Real.add_one_le_exp (v*y^2)]
  change Arc.tail L R m*tuck G^m*(E*Scales.b x^n)^m ≤ _
  rw [mul_assoc]
  apply le_trans (mul_le_mul_of_nonneg_left hb (Arc.tail_pos ..).le)
  unfold Arc.tail; rw [← Real.exp_add]; change Real.exp _ ≤ Real.exp (-v*y^2*_)
  apply Real.exp_le_exp.mpr
  have hi : -t*R^2 ≤ -2*v*y^2 := by
    unfold v rateTrigger; change -t*R^2≤ -2*(t*(θ/2)^2/2)*y^2
    nlinarith only [mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity : 0≤θ/2*y) he 2) ht.le]
  have h' := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg (α:=ℝ) m)
  change -(t)*_ * _ + _ ≤ _
  linarith only [h']

-- Joint late quote, before sampling ANY real step at those heights
structure Gala {G : Gauge} (P : Teller G) (N : Side)
    (u v a M H L Θ K : ℝ) -- u for geometry exponent (called r in Breeze); K for charts
    (x θ E : ℝ) (n k : ℕ) : Prop where
  winter : 0 < u ∧ 0 < v ∧ 0 < a ∧ 0 < M ∧ 0 < H
  covariance : 0<L
  revenue : 1≤Θ
  heat : 0<θ
  polynomial : 0≤E
  atlas : ∀ {I : Type} [Fintype I] [DecidableEq I] {Ω : Type} [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ]
      {C : Gaussian.Table (I × G.ColorIndex)} {η : ℝ}, C.PosSemidef → Numeric C η L →
      ∀ {Ξ : Type} {Y : Finset Ξ} {e : Ξ → I × I} (p j : Finset I) {ρ h : ℝ} {w d : Ξ→ℝ} {r : Ξ→Ω × Prices G I→ℝ},
        Covered e Y w d r L → 0≤ρ → 0≤h →
        ∀ v : Ω × Prices G I → ℝ, Measurable v →
          (∀ y, ‖v y‖ ≤ h*scores p k y.2) → (∀ y, v y≠0 → y.2∈triggered j ρ) →
      let U := μ.prod (cloud C); let f y := v y*wires Y r y
      Integrable f U ∧ (∫ y,‖f y‖ ∂U) ≤ h*Θ*dusk G p.card (2*k)*(Arc.tail L ρ j.card*tuck G^j.card) *
        ∏ i∈Y, (Real.exp (pinch L)*tuck G^2*w i)
  damp : K * fiery G x N ≤ 1
  recall (β : ℝ) : Scales.y G N x /2 ≤ β → 0≤anxious G N x θ β ∧ ∀ m : ℕ,
      Arc.tail L (anxious G N x θ β) m*tuck G^m * (E*(Scales.b x)^n)^m ≤
        Real.exp (-rateTrigger L θ * Scales.p G N x^2*m)
  coast : ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=N →
      100*(1+radiusB x) ≤ c.val → P.Funds S T →
      ∀ β∈ Set.Icc (Scales.y G N x/2) (2*Scales.y G N x),
      ∀ (A : Stores S) (F : Forest S.ratio) (t:S.Choices) (V:Config G c) (q:Chi) (d : ℝ), A.flags=RG.flags (temp x) V →
      0<d → d≤1 → 2*d<firstRadius G → let C:=fog A F T x V t
        C.PosDef ∧ (∃ η : ℝ, Numeric C η L) ∧ ∀ Y, Cradled S T A F t V q x u v a M H (coupling β) d L Y


end YM.AnalyticBridge.AnnulusRatioInsertions.Parade
