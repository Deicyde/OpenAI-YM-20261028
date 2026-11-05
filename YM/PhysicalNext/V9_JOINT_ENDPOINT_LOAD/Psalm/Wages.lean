import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Hiring
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Weighted

/-! # Delay the two-mark polynomial price on the actual entering heights -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm.Solo
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
   Push.SectorMeasure MeasureTheory AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian Heir Suite
   Push.AbsoluteSums Extra.Iteration Extra.Iteration.Scales RG.Supply Testing Push.PriceCompiler Shoot
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {s : Sheet G} {K : MapPrices} {D : Rolls s} {Θ : Protection D}
    {E t : ℕ → ℕ → ℝ} {C : Programs s} {r : ℕ→ℕ→ℕ}

abbrev kiosk (n : ℕ) := Classical.choice (instrument n)
private lemma hit_bound : ∃ K : ℝ,0 ≤ K ∧ ∀ M : ℕ, hitFare M ≤ K*(1+(M:ℝ))^4 := by
  let p := 4*(3:ℝ) -- price of 2*(4B+2)+1
  let a := ((1:ℝ)⁻¹^(4+0) * (4+0).factorial * Real.exp 1)*(1-Real.exp (-1))⁻¹
  have he : 0≤(1-Real.exp (-1))⁻¹ := by have he : Real.exp (-1) < 1 := Real.exp_lt_one_iff.mpr (by norm_num); positivity
  have ha : 0≤a := by unfold a; positivity
  refine ⟨p^4*a,by positivity,fun M => ?_⟩
  unfold hitFare Footprint.payment Footprint.degreeIncome Footprint.spread Animals.ballCost; rw [one_mul,mul_zero,Real.exp_zero,one_mul,one_mul]; push_cast
  have hM : (4*(M:ℝ)+2+(4*(M:ℝ)+2)+1)^4 ≤ (p*(1+(M:ℝ)))^4 := by
    gcongr 1; unfold p; linarith only [Nat.cast_nonneg (α:=ℝ) M]
  refine le_trans (le_of_eq (b:=(4*(M:ℝ)+2+(4*(M:ℝ)+2)+1)^4 *a) (by unfold a; ring)) ((mul_le_mul_of_nonneg_right hM ha).trans_eq (by ring))

structure Reset (E K : ℝ) (L : Side) (G : Gauge) (x : ℝ) : Prop where
  budget : unforced (betaF G x L) ≤ 1
  hit (β : ℝ) : β ∈ Icc (betaF G x L/2) (2*betaF G x L) →
    hitFare (radiusB x)*((E/(L.val:ℝ)) * (K*unforced (betaF G x L)^2)) ≤ min (coupling β) (E/L.val) * unforced (betaF G x L)

theorem sustained (E K : ℝ) (hE : 0 ≤ E) (hK : 0 ≤ K) (L : Side) (G : Gauge) : ∀ᶠ x : ℝ in atTop, Reset E K L G x := by
  obtain ⟨C,hC,h⟩ := hit_bound
  let a := G.slopeConstant*Real.log L.val; have ha : 0≤a := Work.E04.shift_nonneg ..
  have hL : (0:ℝ) ≤ L.val := by positivity
  have hv : ∀ b≥(0:ℝ), Tiny id (fun x : ℝ => b*(1+(radiusB x:ℝ))^4) := fun b he => (Tiny.const tendsto_id _ he).mul (Tiny.cover_size.pow tendsto_id 4) tendsto_id
  filter_upwards [eventually_gt_atTop (1:ℝ),eventually_ge_atTop a, hv (2*C*K*(1+E/L.val)) (by positivity) (1/2) (by norm_num)] with x hx ha' h₀
  have ht := zero_lt_one.trans hx; let δ := unforced (x+a)
  have hh : 0≤δ := by unfold δ unforced Vac.Numbers.Hat; positivity
  have hδ : δ ≤ Vac.Numbers.Hat x ^2 := by
    refine (unforced_mono ht (by linarith)).trans ?_
    rw [unforced,← Real.rpow_natCast]; apply Real.rpow_le_rpow_of_exponent_ge (by unfold Vac.Numbers.Hat; positivity) ?_ (by norm_num)
    exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hx.le)
  have hδ' : δ ≤ 1 := hδ.trans (pow_le_one₀ (by unfold Vac.Numbers.Hat; positivity) (inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hx.le)))
  refine ⟨hδ',fun β hβ => ?_⟩
  have hb : 0 < β ∧ β≤4*x := by obtain ⟨h,h'⟩ := hβ; change (x+a)/2≤β at h; change β≤2*(x+a) at h'; constructor <;> linarith
  have h' : Vac.Numbers.Hat x ≤ 2*coupling β := by unfold Vac.Numbers.Hat coupling; rw [← div_eq_mul_inv,inv_le_comm₀ (Real.sqrt_pos.mpr ht) (by have := hb.1; positivity),inv_div,div_le_iff₀ (zero_lt_two' ℝ)]; nlinarith [Real.sq_sqrt hb.1.le, Real.sqrt_nonneg x, Real.sqrt_nonneg β, Real.sq_sqrt ht.le]
  let f := hitFare (radiusB x); let w := E/(L.val:ℝ); have hw : 0≤w := by unfold w; positivity
  have hf : (f*K*(1+w))*(2*δ) ≤ Vac.Numbers.Hat x := by
    apply le_trans (b:=x^(1/2:ℝ)* (Vac.Numbers.Hat x)^2) ?_ ?_
    · rw [show (f*K*(1+w))*(2*δ)=(2*f*K*(1+w))*δ by ring]; refine mul_le_mul ((show 2*f*K*(1+w) ≤ _ from ?_).trans h₀.2) hδ hh (by positivity)
      unfold w f; apply le_trans _ (le_of_eq (by ring) : (2*(C* (1+(radiusB x:ℝ))^4)*K*(1+E/(L.val:ℝ))) ≤ _); gcongr; exact h _
    rw [← Real.sqrt_eq_rpow,Vac.Numbers.Hat]; field_simp; rfl
  change f*(w*(K*δ^2)) ≤ min _ w * δ
  have he : f*(w*(K*δ)) ≤ min (coupling β) w := by
    refine le_min ?_ ?_
    · have h : f*K*δ ≤ 0 ∨ 0 ≤ f*K*δ := le_total ..
      rcases h with h|h; · nlinarith only [mul_nonpos_of_nonpos_of_nonneg h hw,coupling_pos hb.1]
      nlinarith only [hf,h',h]
    have h'' : Vac.Numbers.Hat x ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hx.le)
    by_cases h : f*K*δ<0
    · nlinarith only [mul_nonpos_of_nonpos_of_nonneg h.le hw,hw]
    nlinarith only [mul_le_mul_of_nonneg_right hf hw,mul_le_mul_of_nonneg_right h'' hw,mul_nonneg (not_lt.mp h) (sq_nonneg w),hw]
  nlinarith only [mul_le_mul_of_nonneg_right he hh]

def Sustained (W : Delays Θ) (E : ℕ → ℕ → ℝ) := ∀ j x,W.betaEntry j ≤ x → ∀ i, StepStages j i → Reset (E j i) (kiosk (s.profile j).order).bid (D.L j) G x
lemma sustain (U : Delays Θ) (h : Earlier s K C E t r) : ∃ W : Delays Θ, DelayLe U W ∧ OrderedDelays W ∧ ∀ W', DelayLe W W' → Sustained W' E := by
  obtain ⟨W,hW,ho,h'⟩ := delay_extra U _ (fun _ _ _=>True) (fun j => eventually_transitions j _ _ fun i _ => sustained (E j i) (kiosk (s.profile j).order).bid
    (zero_le_one.trans (h.agrees j i).2.2.nonneg) (zero_le_one.trans (kiosk (s.profile j).order).large) (D.L j) G) (by simp)
  exact ⟨W,hW,ho,fun W h => (h' W h).1⟩
end YM.PhysicalNext.JointLoad.Psalm.Solo
