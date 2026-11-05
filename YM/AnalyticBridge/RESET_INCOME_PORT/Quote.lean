import YM.AnalyticBridge.RESET_INCOME_PORT.Tail

set_option warningAsError false

/-!
# Prerequisite pricing tests on one realized plate

Use especially where about to issue a raw Split. Comparators / prices are
*parameters*, e.g. from determinant, tail and local logarithm analysis. An
optional log-density test for the core reference never takes a log of a
possibly zero kernel, a door or a signed gas. All numerator prices are at
the same scalar/predictor that is going to be tested, BEFORE modifying β or
v. Work per Store AND tag, not a threshold implication on abstract fields.
These are fixed finite-volume/order-zero tests; numerical caps expose how
many of these errors would really have to add, *not* asserting a Split with
head = just an apparently good sector at all periods could actually pay
these. For uniform-in-period deployment a log price from a reorganized gas
(e.g., HeadGas in this module series) can be much more appropriate than
this price. See LocalPrice for composing order-zero local budgets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome

open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Rows
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

namespace Plate
variable (e : Plate G S) (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices)

def posLog (z : e.Sample A) :=
  let q := e.center A V k z.1
  let l := q + coupling R.beta • z.2
  let U := e.image R A V k z
  Real.log (reserve e.chip e.chart e.d (tape l)) -
    averaged (fun s => reduced R (till e.x) (pull s 0 U)) - R.activities.additive R.p U +
    coarseTail e.tube e.x e.point V R.beta - R.beta *
    averaged (Rows.residual e.tube e.x V k (shots S e.x) A e.forest e.chip e.d z.1 U l) +
    adjustment e.tube e.x V k (shots S e.x) A e.forest e.chip e.d z.1 (e.Cov A V k) q (coupling R.beta) z.2

def screen (z : e.Sample A) :=
  let U := e.image R A V k z
  doors e.chip e.d (displaced (e.center A V k z.1) (coupling R.beta) z.2) * e.book.bill A k U V * S.likelihood U k

def signed (z : e.Sample A) := e.screen R A V k z * R.activities.gas R.p (e.image R A V k z)



lemma color_prices (z : e.Sample A) :
    e.color R A V k z = Real.exp (e.posLog R A V k z) * e.signed R A V k z := by
  unfold posLog color sleeves signed screen image displaced
  simp only [uncurry, sub_eq_add_neg, Real.exp_add, Real.exp_log (reserve_pos ..)]; ring
end Plate

/-- Log-pair prices, Gram (relative to the one FLAT det) and Gram*Cov
(the nonsymmetric one), on the one region respectively. Units full volume;
use e.g., local block estimates paying a sum across the windows to provide
`Pays` below. No eigen log on the second input. -/
structure Quote where
  main : ℝ
  trab : ℝ
  high : ℝ
  bend : ℝ

variable (e : Plate G S) (R : Rep G f) (A : Stores S) (V : Config G c) (k : S.Choices)
namespace Quote
variable (w : Quote)

def assessment := -(Fintype.card (Frozen A e.x e.forest) : ℝ) * Real.log (spare e.chart R.beta) -
    (1/2) * w.main + (1/2) * w.trab

def tip := (w.high + w.bend) / 2

structure Pays (w : Quote) (e : Plate G S) (A : Stores S) (V : Config G c) (k : S.Choices) : Prop where
  one : |(Real.log (e.Gram A V k).det - Real.log e.Flat.det) - w.main| ≤ w.high
  two : |Real.log (1 + (e.Gram A V k * e.Cov A V k - 1)).det - w.trab| ≤ w.bend

lemma adjust (h : w.Pays e A V k) : |e.cost R A V k - w.assessment e R A| ≤ w.tip := by
  obtain ⟨h1,h2⟩ := abs_le.mp h.one; obtain ⟨h3,h4⟩ := abs_le.mp h.two
  unfold Plate.cost assessment tip; exact abs_le.mpr ⟨by linarith,by linarith⟩
end Quote

/-- Amount still to be supplied by signed multiplier, relative (log leading
forecast units at the output) to `u`. `posLog` is the only log-price of the
*integrand* inside this formula. The dets need a separate Quote.Pays. -/
def shipped (q : Quote) (u : ℝ) (z : e.Sample A) := e.outside R V + q.assessment e R A - u + e.posLog R A V k z

/-- Prescriptions not asserted to exist. The comparison mass uses the
SAME cloud law, can include mask/probability factors. `slack` will be
needed on the comparison support only. For a reference strictly zero in
some regions, the `ports` test then bills the entire absolute numerator
there, normalized at the same q,u it uses elsewhere. -/
structure Coupon (e : Plate G S) (A : Stores S) where
  q : Quote
  seen : e.Sample A → ℝ
  lens : e.Sample A → ℝ  -- LOG baseline of terms in shipped
  miss : e.Sample A → ℝ
  slack : ℝ
  weight : ℝ
  extra : ℝ

namespace Coupon
variable {e A}
variable (w : Coupon e A)

def base (z : e.Sample A) := Real.exp (w.lens z) * w.seen z

def down := Real.exp (-(w.slack+w.q.tip)) * w.weight - Real.exp w.q.tip * w.extra

def up := Real.exp (w.slack+w.q.tip)*w.weight + Real.exp w.q.tip*w.extra

/-- Pointwise tests on the raw integrations and their prices. Need the log
error only where comparison mass is present. No uniform smallness premise
on actual output normalized evaluator, signed sector sums or their ratios.
Still a strong condition. In particular `mass` would have to be paid for
the actual comparison integral, not just relative to a hypothesized
Gaussian unknown determinant. -/
structure Uses (w : Coupon e A) (R : Rep G f) (V : Config G c) (k : S.Choices) (u : ℝ) : Prop where
  det : w.q.Pays e A V k
  pos : ∀ᵐ z ∂(e.law A V k), 0 ≤ w.seen z
  bill : Integrable w.base (e.law A V k)
  mass : (∫ z, w.base z ∂(e.law A V k)) = w.weight
  errlog : ∀ᵐ z ∂(e.law A V k), w.seen z ≠ 0 → |shipped e R A V k w.q u z - w.lens z| ≤ w.slack
  ports : ∀ᵐ z ∂(e.law A V k), Real.exp (shipped e R A V k w.q u z) * |e.signed R A V k z - w.seen z| ≤ w.miss z
  monitor : Integrable w.miss (e.law A V k)
  surplus : (∫ z, w.miss z ∂ (e.law A V k)) ≤ w.extra

private lemma compare {r m g h b K H M E D : ℝ} (hg : 0 ≤ g) (hb : g ≠ 0 → |r-h| ≤ b)
    (hv : Real.exp r * |m-g| ≤ M) (hK : |K-H| ≤ D) (he : E=K-H+r) :
    Real.exp E*m ∈ Icc (Real.exp (-(b+D))*(Real.exp h*g) - Real.exp D * M)
      (Real.exp (b+D)*(Real.exp h*g) + Real.exp D * M) := by
  have hm : 0 ≤ M := (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)).trans hv
  have hx : |Real.exp E*(m-g)| ≤ Real.exp D*M := by
    rw [he,abs_mul,abs_of_pos (Real.exp_pos _),Real.exp_add,mul_assoc]
    exact (mul_le_mul_of_nonneg_left hv (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (le_of_abs_le hK)) hm)
  have ht : Real.exp (-(b+D))*(Real.exp h*g) ≤ Real.exp E*g ∧
      Real.exp E*g ≤ Real.exp (b+D)*(Real.exp h*g) := by
    by_cases hh : g=0
    · simp [hh]
    have ⟨ha,hA⟩ := abs_le.mp (hb hh)
    have ⟨hc,hC⟩ := abs_le.mp hK
    rw [←mul_assoc,←mul_assoc (Real.exp (b+D)),←Real.exp_add,←Real.exp_add]
    exact ⟨mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hg,
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hg⟩
  obtain ⟨ha,hA⟩ := abs_le.mp hx
  rw [mul_sub] at ha hA; exact ⟨by linarith only [ha,ht.1],by linarith only [hA,ht.2]⟩

variable {R V k} {u : ℝ}
lemma Uses.cashed {w : Coupon e A} (he : e.Receipt R) (hm : e.matched A V) (h : w.Uses R V k u) :
    Real.exp (e.outside R V-u)*e.value R A V k ∈ Icc w.down w.up := by
  let s := e.cost R A V k
  let y := e.outside R V-u+s
  let L z := Real.exp y * e.color R A V k z
  have hp : Integrable L (e.law A V k) := (Plate.integrable_color he A V k).const_mul _
  let F z := Real.exp (-(w.slack+w.q.tip))*w.base z
  let H z := Real.exp (w.slack+w.q.tip)*w.base z
  let T z := Real.exp w.q.tip*w.miss z
  have hF := h.bill.const_mul (Real.exp (-(w.slack+w.q.tip))); have hH := h.bill.const_mul (Real.exp (w.slack+w.q.tip))
  have hT := h.monitor.const_mul (Real.exp w.q.tip)
  have hx : ∀ᵐ z ∂(e.law A V k), F z - T z ≤ L z ∧ L z ≤ H z + T z := by
    filter_upwards [h.pos,h.errlog,h.ports] with z hg hb hv
    unfold L; rw [Plate.color_prices,←mul_assoc,←Real.exp_add]
    exact compare hg hb hv (w.q.adjust e R A V k h.det) (by unfold y shipped s; ring)
  have h0 := integral_mono_ae (hF.sub hT) hp (hx.mono fun z hh => hh.1)
  have h1 := integral_mono_ae hp (hH.add hT) (hx.mono fun z hh => hh.2)
  rw [Plate.value, if_pos hm, ←mul_assoc, ← Real.exp_add]
  simp only [Pi.sub_apply] at h0; simp only [Pi.add_apply] at h1
  rw [integral_sub hF hT] at h0; rw [integral_add hH hT] at h1
  simp_rw [integral_const_mul, h.mass] at h0 h1
  have h2 := mul_le_mul_of_nonneg_left h.surplus (Real.exp_pos w.q.tip).le
  change _ ≤ ∫ z, Real.exp y * _ ∂_ at h0; change (∫ z, Real.exp y * _ ∂ _) ≤ _ at h1
  rw [integral_const_mul] at h0 h1
  exact ⟨(sub_le_sub_left h2 _).trans h0,h1.trans (add_le_add_right h2 _)⟩
end Coupon

/-- Stronger bill on an outer selected Store. No dropping the earned
charge correction. There needn't exist a uniformly applicable outer
selection with these besides putting all Stores in the head! See also
E fsect:freset, where even many apparently unimportant contributors can
be important in pricing the log (large periods). -/
structure Tariff (e : Plate G S) (A : Stores S) where
  q : Quote
  test : e.Sample A → ℝ
  extra : ℝ
namespace Tariff
variable {e A}

def ceiling (w : Tariff e A) := Real.exp w.q.tip*w.extra

structure Paid (w : Tariff e A) (R : Rep G f) (V : Config G c) (k : S.Choices) (u κ : ℝ) : Prop where
  det : w.q.Pays e A V k
  probe : ∀ᵐ z ∂(e.law A V k), Real.exp (shipped e R A V k w.q u z) * |e.signed R A V k z| *
    e.reverseFee R A V k κ (e.image R A V k z) ≤ w.test z
  monitor : Integrable w.test (e.law A V k)
  pays : (∫ z, w.test z ∂(e.law A V k)) ≤ w.extra

variable {R V k} {u κ : ℝ}
lemma Paid.cashes {w : Tariff e A} (he : e.Receipt R) (hm : e.matched A V) (h : w.Paid R V k u κ)
    {P : Teller G} (hP : P.Funds S e.tube) :
    Real.exp (e.outside R V-u)*e.expense R A V k κ ≤ w.ceiling := by
  let s := e.cost R A V k; let y := e.outside R V-u+s
  rw [Plate.expense,if_pos hm,←mul_assoc,←Real.exp_add,←integral_const_mul]
  let t := w.q.tip
  have hp : 0 ≤ Real.exp t := (Real.exp_pos _).le
  calc
    _ ≤ ∫ z, Real.exp t*w.test z ∂(e.law A V k) := by
      apply integral_mono_ae ((e.recoil_int R A V k he hP κ).const_mul _) (h.monitor.const_mul _)
      filter_upwards [h.probe] with z hz
      let X := e.reverseFee R A V k κ (e.image R A V k z); have hX : 0 ≤ X := (Real.exp_pos _).le
      unfold Plate.recoil; rw [Plate.color_prices,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le,Real.norm_eq_abs]
      calc
        _ = Real.exp (s-w.q.assessment e R A)*(Real.exp (shipped e R A V k w.q u z)* |e.signed R A V k z| *X) := by
          unfold shipped X; simp only [Real.exp_add,Real.exp_sub,s]; field_simp
        _ ≤ Real.exp t*(Real.exp (shipped e R A V k w.q u z)*|e.signed R A V k z| *X) := mul_le_mul_of_nonneg_right
          (Real.exp_monotone (le_of_abs_le (w.q.adjust e R A V k h.det))) (mul_nonneg (by positivity) hX)
        _ ≤ _ := mul_le_mul_of_nonneg_left hz hp
    _ ≤ _ := by rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left h.pays hp
end Tariff
end YM.AnalyticBridge.ResetIncome
