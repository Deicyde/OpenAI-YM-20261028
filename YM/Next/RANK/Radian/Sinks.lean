import YM.Bid.Loan
import YM.Next.RANK.Radian.Boilers
import YM.Next.RANK.Radian.Heat

/-!
# Integrate symbol remainder jet estimate

At this port prefer admitting census with also global far-derivative decay gates
(free stamped symbol may always have compact support around chosen representatives); uncompact HeatP ok.
No smoothness assertions at ZERO. Values there for finite-grid comparisons later. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice  Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {n D : ℕ} {F G : E4→ℂ} {U : Set E4} {C c r M : ℝ}

-- jets. n here is sum of endpoint spatial orders
structure Mist (F : E4→ℂ) (k : ℕ) (C : ℝ) : Prop where
  part : ContDiffOn ℝ (↑(k+6:ℕ)) F away
  jet (v : ℕ) (h : v≤k+6) (x : E4) (hx : x≠0) (hv : ‖x‖ ≤ 1) : ‖iteratedFDeriv ℝ v F x‖ * ‖x‖^v ≤ C* ‖x‖^(k+1)
  far (v : ℕ) (h : v≤k+6) (x : E4) (hx : 1 ≤ ‖x‖) : ‖iteratedFDeriv ℝ v F x‖ ≤ C/‖x‖^5

def reach (r : ℝ) (x : E4) := if r/2 ≤ ‖x‖ then (‖x‖^5)⁻¹ else 0
lemma therein (x:E4) (r : ℝ) : 0 ≤ reach r x:= by unfold reach;split;positivity;exact le_rfl
lemma scales_reach {r : ℝ} (h : 0 < r) (x : E4) : reach r x=(r^5)⁻¹*reach 1 (r⁻¹ • x) := by
  have ht : ‖r⁻¹ • x‖=‖x‖/r := by rw [norm_smul,norm_inv,Real.norm_of_nonneg h.le,div_eq_inv_mul]
  unfold reach;rw [ht]; have hx:1/2≤ ‖x‖/r ↔ r/2 ≤ ‖x‖:= by rw [le_div_iff₀ h]; ring_nf
  by_cases hy:r/2≤‖x‖
  · rw [if_pos hy,if_pos (hx.mpr hy)]; field_simp
  rw [if_neg hy,if_neg (mt hx.1 hy),mul_zero]
lemma reaches : Integrable (reach 1):= by
  have ht : Integrable (fun v:E4=> (1+‖v‖)^(-(5:ℝ))):= integrable_one_add_norm (by rw [spaceD]; norm_num)
  have hh : Measurable (reach 1):= by unfold reach; apply Measurable.ite _ (continuous_norm.measurable.pow_const _|>.inv) measurable_const; exact (isClosed_le continuous_const continuous_norm).measurableSet
  refine (ht.const_mul (3^5)).mono' hh.aestronglyMeasurable (Eventually.of_forall fun x=> ?_)
  rw [Real.norm_of_nonneg (therein ..)]; unfold reach;split
  · rename_i h;have he:0<‖x‖:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) h
    change (‖x‖^5)⁻¹ ≤ (3:ℝ)^5*(1+‖x‖)^(-(5:ℝ)); rw [Real.rpow_neg (by positivity), Real.rpow_ofNat]
    field_simp; rw [mul_comm (‖x‖^5)]; apply le_trans _ (le_of_eq (show (3*‖x‖)^5=(3:ℝ)^5*‖x‖^5 by rw [mul_pow])); gcongr;linarith
  positivity
lemma reaching {r : ℝ} (h : 0 < r) : Integrable (reach r):= by
  rw [show reach r= (fun i=> _) from funext (scales_reach h)]; exact (Integrable.comp_smul reaches (show r⁻¹≠0 by positivity)).const_mul _
lemma slope (h : 0 < r) : (∫ x,reach r x)=(∫ x,reach 1 x) / r:= by
  simp_rw [scales_reach (r:=r) h]; rw [integral_const_mul,Measure.integral_comp_inv_smul,spaceD,abs_of_nonneg (by positivity),smul_eq_mul];field_simp

lemma evening_zero (h : 0< r) (F : E4→ℂ) {i : E4} (hp : ‖i‖<r/2) : sail r * F =ᶠ[𝓝 i] fun _=> (0:ℂ):= by
  filter_upwards [(Metric.isOpen_ball.mem_nhds (x:=i) (show i∈ Metric.ball 0 (r/2) from by simpa using hp))] with j hj
  have hh : ‖j‖ ≤ r/2 := le_of_lt (show ‖j‖<r/2 from by simpa using hj)
  change ((1:ℂ)-_)*_= _;rw [stalls h hh,sub_self,zero_mul]
lemma evening_smooth (h : 0<r) (hp : ContDiffOn ℝ (↑n) F away): ContDiff ℝ (↑n) (sail r*F):= contDiff_iff_contDiffAt.mpr fun i=> by
  by_cases he:i=0
  · subst i; apply contDiffAt_const.congr_of_eventuallyEq; exact evening_zero h F (show ‖(0:E4)‖<r/2 by simp only [norm_zero]; linarith only [h])
  exact ((away_sail _).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)).mul ((hp i he).contDiffAt (open_away.mem_nhds (show i∈away from he)))

lemma untouched (h : 0 < r) (F : E4→ℂ) {i : E4} (hp : r < ‖i‖) : sail r*F=ᶠ[𝓝 i] F:= by
  filter_upwards [continuous_norm.continuousAt.eventually (lt_mem_nhds hp)] with j hj
  change ((1:ℂ)-_)*_= _; have ht:r ≤ ‖j‖:=le_of_lt hj; rw [fades_out h ht,sub_zero,one_mul]
-- use all-point derivative cost. v≤n
lemma penny (h : Mist F D C) (hq : 0≤C) (j) (hj : j≤D+6) (x : E4) (hx : x≠0) :
    ‖iteratedFDeriv ℝ j F x‖ ≤ C / ‖x‖^5 := by
  by_cases he:1 ≤ ‖x‖; exact h.far j hj x he
  have hy:0 < ‖x‖:= norm_pos_iff.mpr hx
  apply (le_div_iff₀ (pow_pos hy _)).2; apply le_of_mul_le_mul_right (a:=‖x‖^j) _ (pow_pos hy _)
  have ht:‖x‖^(D+1)*‖x‖^5 ≤ ‖x‖^j := by rw [← pow_add];exact pow_le_pow_of_le_one hy.le (le_of_not_ge he) hj
  linarith only [mul_le_mul_of_nonneg_right (h.jet j hj x hx (le_of_not_ge he)) (pow_nonneg hy.le 5),mul_le_mul_of_nonneg_left ht hq]

lemma dark {i : E4} (p : ‖i‖ < r/2) (hr : 0<r) (j) : iteratedFDeriv ℝ j (sail r * F) i=0:= by
  rw [((evening_zero hr F p).iteratedFDeriv ℝ j).eq_of_nhds]; simp

lemma settles (n : ℕ) : ∃ K : ℝ, 1 ≤ K ∧ ∀ j≤ n+6,∀ F C (_ : Mist F n C) (_ : 0≤C) r (_ : 0< r), r≤1 → ∀ x,
    ‖iteratedFDeriv ℝ j (sail r*F) x‖ ≤ C*K*reach r x:= by
  obtain ⟨t,hT,ht⟩:= crown_cost (n+6)
  refine ⟨2^(n+6)*t,one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hT,?_⟩
  intro j hj F C h hv r hr ht' x
  have hz:C ≤ C*(2^(n+6)*t):= le_mul_of_one_le_right hv (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hT)
  unfold reach; split
  · rename_i hq;have hy :0<‖x‖ := lt_of_lt_of_le (by positivity : 0 < r/2) hq
    have he:x≠0 := norm_pos_iff.mp hy
    by_cases hL:r < ‖x‖
    · rw [((untouched hr F hL).iteratedFDeriv ℝ j).eq_of_nhds];exact (penny h hv j hj x he).trans (by rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right hz (inv_pos.mpr (pow_pos hy _)).le)
    have hK:‖x‖ ≤ r:= le_of_not_gt hL
    have ha (i) (hp : i≤ j): ‖iteratedFDeriv ℝ i (sail r) x‖ * ‖iteratedFDeriv ℝ (j-i) F x‖ ≤ C * t * (‖x‖^5)⁻¹:= by
      let q:= ‖x‖; let v:= ‖iteratedFDeriv ℝ i (sail r) x‖; let w:= ‖iteratedFDeriv ℝ (j-i) F x‖
      have h₁ : v*q^i ≤ t:= by
        have hh:=ht i (hp.trans hj) r hr x
        apply le_trans (b:=v*r^i) _ ((le_div_iff₀ (pow_pos hr _)).1 hh);gcongr
      have h₂ : w*q^(j-i) ≤ C*q^(n+1):= h.jet _ (by omega) x he (hK.trans ht')
      rw [← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos hy 5)).2; apply le_of_mul_le_mul_right (a:=q^j) _ (pow_pos hy j)
      have ht : q^(n+1)*q^5 ≤ q^j:= by rw [← pow_add];exact pow_le_pow_of_le_one hy.le (hK.trans ht') hj
      have hs : 0≤ w:=norm_nonneg _
      have hh:=mul_le_mul_of_nonneg_right (mul_le_mul h₁ h₂ (mul_nonneg hs (pow_pos hy _|>.le)) (zero_le_one.trans hT)) (pow_nonneg hy.le 5)
      change v*w*q^5 *q^j ≤ _ ; calc
        _ = v*q^i*(w*q^(j-i)) * q^5:= by
          conv_lhs=> rw [show q^j=q^i*q^(j-i) by rw [← pow_add, Nat.add_sub_of_le hp]]
          ring
        _ ≤ t*(C*q^(n+1))*q^5:= hh
        _ ≤ _:= by nlinarith only [mul_le_mul_of_nonneg_left ht (mul_nonneg hv (zero_le_one.trans hT))]
    apply (stove away open_away ((away_sail r).contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)) (h.part.of_le (by exact_mod_cast hj)) x he).trans
    apply le_trans (b:=∑ i∈Finset.range (j+1),(j.choose i:ℝ)*(C*t*(‖x‖^5)⁻¹)); refine sum_le_sum fun i hi=>?_ ; rw [mul_assoc];exact mul_le_mul_of_nonneg_left (ha _ (Nat.le_of_lt_succ (mem_range.mp hi))) (by positivity)
    rw [← sum_mul, ← Nat.cast_sum,Nat.sum_range_choose]; push_cast
    apply le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : 1≤(2:ℝ)) hj) (by positivity : 0 ≤ C*t*(‖x‖^5)⁻¹)); exact le_of_eq (by ring)
  rename_i hh; rw [dark (lt_of_not_ge hh) hr, norm_zero,mul_zero]
end YM.Next.Rank.Radian
