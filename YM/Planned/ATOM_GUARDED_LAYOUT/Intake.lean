import YM.Extra.SOURCE_HISTORIES.Purchase
import YM.Planned.ATOM_GUARDED_LAYOUT.Orbit
import YM.Push.LOCAL_SPLITTING.Step


/-!
# Conversion with split intake prices

Only quantifies estimates on the *unconverted* expansion at the output
anchor and a model there. The clients can use the estimate before even
performing Jmdef: no residual norm, adapted presentation at each orientation,
or bound on the converted coordinates needs to be supplied. In particular,
for the Histories **rate on remainder atoms**, *no* small lead error
estimate separate from the raw bulk prices (and any seed price) is
required. E's independent coupling-small coordinate estimate on old
remainders can be important for other goals.

`Tare` is the separated version of Local's `Raw.Income`. The second producer
at the end pays these bills from old-support prices with the working +2
reserve and width delay of `income_of_reserved`. Winding outputs still
have to pay the stated genuine bills (including zeroth order) and take
the wrapping read as in Local. No mask derivatives, nor any assumption
like agreement of analytic germs across a flag read.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Planned.GuardedAtom
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories Motion
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
  {M : Raw F n} {R : Rep G n} {X : ℕ → Support n} {o : Site n} {A : Hol G} {B : SectionData F}
  {w v κ a b c paid : ℝ}

/-- Local `Income` as SEPARATE bills at the same e. Collect sufficient
bulk and meeting costs before doing `Raw.build`. `b,c` already divided
by current forced divisor. -/
structure Tare (M : Raw F n) (o : Site n) (X : ℕ → Support n) (A : Hol G) (B : SectionData F) (R : Rep G n)
    (w v κ a b c : ℝ) : Prop where
  bulk : ∃ e, M.cost o X R.p e ∧ SumBudget (fun i => Raw.rawMass A B o (X i) R.p w (e i)) a ∧
    SumBudget (fun i => Raw.rawMerge A B o (X i) R.p w v (e i)) (κ*c)
  packets : ForceCost R.p R.activities M.forced (κ*b)

/-- Old-support (before the join with the canonical stencil) sufficient
bulk bid. `b` charges unconverted forced terms *on that same alphabet*.
For the +2 reserve only a width * forcedAllowance bound is needed;
divide by κ explicitly below. -/
structure Deck (M : Raw F n) (o : Site n) (X : ℕ → Support n) (R : Rep G n) (κ a b : ℝ) : Prop where
  bulk : ∃ e, M.cost o X R.p e ∧ SumBudget (fun i => reservedMass R.p (X i) (e i)) a
  packets : ForceCost R.p R.activities M.forced (κ*b)

lemma sumBudget_credit {ι : Type*} {f : ι → ℝ} (h : SumBudget f c) : 0 ≤ c :=
  (tsum_nonneg h.1).trans h.2.2

lemma ForceCost_credit {f : ℕ → Config G n → ℂ} (h : ForceCost R.p R.activities f c) : 0 ≤ c := by
  obtain ⟨e,he,-⟩ := h
  exact sumBudget_credit he

namespace Tare
variable (h : Tare M o X A B R w v κ a b c)
include h

lemma costs_nonneg (hκ : 0 < κ) : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c := by
  obtain ⟨e,-,ha,hc⟩ := h.bulk
  exact ⟨sumBudget_credit ha,nonneg_of_mul_nonneg_right (ForceCost_credit h.packets) hκ,
    nonneg_of_mul_nonneg_right (sumBudget_credit hc) hκ⟩

lemma income (hκ : 0 < κ) (he : a+(b+c) ≤ paid) : Raw.Income M o X A B R w v κ paid :=
  ⟨a,b,c,(h.costs_nonneg hκ).1,(h.costs_nonneg hκ).2.1,(h.costs_nonneg hκ).2.2,he,h.bulk,h.packets⟩

lemma row_cost (hr : Readable A B R.p n w) (hf : M.Format o X R) :
    SumBudget (fun i => F.coeffSize (M.row o X A R.p.threshold i)) a := by
  obtain ⟨e,h1,h2,-⟩ := h.bulk
  refine sumBudget_mono h2 (fun _ => Work.G08.size_nonneg F _) (fun i => ?_) le_rfl
  have hw := hr.nonneg
  have hx : readPrice A F ≤ atomPrice A F w := by
    unfold atomPrice; nlinarith [readPrice_pos A F]
  have hv := mul_le_mul_of_nonneg_right hx (h1 i).1
  apply (weighted_bound A F o (hf.regular i) hr.order hr.power (h1 i)).trans
  exact hv.trans (R.p.loMass _ _ (mul_nonneg (zero_le_one.trans (atomPrice_ge_one A F hw)) (h1 i).1))

variable (S : Slots R.activities (fun i => joint B o (X i)))

lemma canonical_cost (hr : Readable A B R.p n w) (hf : M.Format o X R) (y : F.Coeff) :
    F.coeffSize ((M.build o X A B R S).x - y) ≤ F.coeffSize (M.seed - y) + a := by
  have he := h.row_cost hr hf
  let U := ∑' i, M.row o X A R.p.threshold i
  change F.coeffSize (M.seed + U - y) ≤ _
  rw [add_sub_right_comm]
  exact (Size.add ..).trans (add_le_add_right ((Size.bound F he.2.1).trans he.2.2) _)

/-- Precise split tab underlying Local `Raw.build_remBound`. Uses Local's
actual estimate `forceCost` on bookings of meeting occurrences. -/
lemma tab (hκ : 0 < κ) (he : R.activities.KBound R.p v) (hr : Readable A B R.p n w) (hf : M.Format o X R) :
    Tab (M.build o X A B R S) o R κ a (b+c) := by
  obtain ⟨e,h1,h2,h3⟩ := h.bulk
  have hi i := charge_atom o hr (hf.regular i) (h1 i)
  have hv := h.packets.add (S.forceCost he h3 (fun i => mul_nonneg (zero_le_one.trans (atomPrice_ge_one A F hr.nonneg)) (h1 i).1) (fun i => (hi i).2))
  obtain ⟨ha,hb,hc⟩ := h.costs_nonneg hκ
  exact ⟨hκ,ha,add_nonneg hb hc,⟨fun i => atomPrice A F w * e i,h2,fun i => (hi i).1⟩,by rwa [mul_add]⟩
end Tare

namespace Deck
variable (h : Deck M o X R κ a b)
include h

lemma costs_nonneg (hκ : 0 < κ) : 0 ≤ a ∧ 0 ≤ b := by
  obtain ⟨e,-,ha⟩ := h.bulk
  exact ⟨sumBudget_credit ha,nonneg_of_mul_nonneg_right (ForceCost_credit h.packets) hκ⟩

/-- Exposed conversion from the old-support reserve to the three costs;
separates that part of `income_of_reserved`. Also allows arbitrary positive
κ (e.g. if another consumer wants a sharper forced rate and **prices** it).
Histories consumers below require varkappa = sqrt(forcedAllowance), not arbitrary. -/
lemma tare (hκ : 0 < κ) (hv : 0 ≤ v) (he : hitWidth R.p * v ≤ 1) (hr : Readable A B R.p n w) (hf : M.Format o X R) :
    let D := factor A B R.p.supportExponent w
    Tare M o X A B R w v κ (D*a) b (hitWidth R.p*v/κ * (D*a)) := by
  intro D
  obtain ⟨e,h1,h2⟩ := h.bulk
  let z i := atomPrice A F w * e i
  have hP := atomPrice_ge_one A F hr.nonneg
  have ht i : 0 ≤ z i := mul_nonneg (zero_le_one.trans hP) (h1 i).1
  have hD : 0 ≤ D := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hP)
  have hh := sumBudget_mul_left h2 hD
  have hy i := price_join B A o (B:=R.p) (hf.origin i) hr.sound hr.nonneg (h1 i).1
  have hQ : 0 ≤ hitWidth R.p*v := mul_nonneg (zero_le_one.trans (width_one_le _)) hv
  refine ⟨⟨e,h1,sumBudget_mono hh (fun i => (ht i).trans (R.p.loMass _ _ (ht i))) (fun i => ?_) le_rfl,
    sumBudget_mono (sumBudget_mul_left hh hQ) (fun i => mergePrice_nonneg _ _ hv (ht i)) (fun i => ?_) ?_⟩,h.packets⟩
  · refine le_trans ?_ (hy i)
    exact mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (ht i)
  · exact (price_meeting hv he (ht i) (joint B o (X i))).trans (mul_le_mul_of_nonneg_left (hy i) hQ)
  exact le_of_eq (by field_simp)

omit h
/-- In the usual width delay, the third Tare bill costs at most the
first (with this Deck). Compare also `income_of_reserved`. -/
lemma usual {h : Deck M o X R (Real.sqrt v) a b} (hv : 0 < v) (hw : hitWidth R.p * Real.sqrt v ≤ 1)
    (hr : Readable A B R.p n w) (hf : M.Format o X R) :
    let D := factor A B R.p.supportExponent w
    Tare M o X A B R w v (Real.sqrt v) (D*a) b (D*a) := by
  intro D
  have hz := Real.sqrt_pos.mpr hv
  have hx : Real.sqrt v ≤ 1 := (le_mul_of_one_le_left hz.le (width_one_le _)).trans hw
  have hp : hitWidth R.p*v ≤ Real.sqrt v := by
    nth_rw 1 [← Real.mul_self_sqrt hv.le,← mul_assoc]
    exact mul_le_of_le_one_left hz.le hw
  obtain ⟨e,h1,h2,h3⟩ := (h.tare hz hv.le (hp.trans hx) hr hf).bulk
  have hP := atomPrice_ge_one A F hr.nonneg
  have hD : 0 ≤ D := mul_nonneg (Real.exp_pos _).le (zero_le_one.trans hP)
  refine ⟨⟨e,h1,h2,sumBudget_mono h3 h3.1 le_rfl ?_⟩,h.packets⟩
  apply mul_le_mul_of_nonneg_left _ hz.le
  exact mul_le_of_le_one_left (mul_nonneg hD (h.costs_nonneg hz).1) ((div_le_one hz).mpr hp)
end Deck

/-! Price at center with ONE `H.Conv`, pre-split data, and model or
small-seed comparison. -/
section block
variable {H : History G} {N p j : ℕ}
variable {g : Config G (H.S.side (j+1) p) → ℂ}
  {lead : F.Coeff} {a b c q r ε : ℝ}
  {X : ℕ → Support (H.S.side j p)} {M : Raw F (H.S.side j p)}
local notation "Cur" => H.rep N p j
local notation "Scale" => H.levels.clock.forcedAllowance j

/-- A Local `Models` hypothesis (estimates on the *pre-conversion*
bulk germs, at the identity only) suffices for the direction port.
Use this e.g. on primary inputs. Only nil-direction input; orientation
loss is anticipated in h₁ (also h₂ on remainder). -/
theorem paid_via_model (S : Slots (Cur).activities (fun i => joint B 0 (X i))) (h : H.Conv N p j)
    (hr : Readable A B (Cur).p (H.S.side j p) w) (hf : M.Format 0 X Cur)
    (he : M.eval 0 X B Cur = blast H N p j d g)
    (hx : Tare M 0 X A B Cur w Scale (kappa H j) a b c)
    {u : ℕ → Directions G (H.S.side j p) → ℂ} (hm : Models A 0 X (Cur).p M lead ε u) (hε : 0 ≤ ε)
    (h₁ : orbitCost F*(errorPrice A F * ε) ≤ q) (h₂ : turnCost (Cur).p.order (Cur).p.power*a+(b+c) ≤ r) :
    PaidAtom B H N p j A g lead q r := by
  have hk := Real.sqrt_pos.mpr (forcedPos H.levels j)
  have hd := (Raw.build_density S h.good hr hf (hx.income hk le_rfl) hk).trans he
  have ht := compareModels S hr hf (Size.series F (hx.row_cost hr hf).2.1).of_norm hε hm
  apply paid_center (fun s => h.good.labels.moves s 0) hr.sound (Raw.build_format S h.good.labels.forced hr hf) hd
    (hx.tab S hk h.good.labels.boundK hr hf) _ h₂
  exact (mul_le_mul_of_nonneg_left ht (zero_le_one.trans (orbitCost_one_le F))).trans h₁

/-- Cheaper port sufficient for the entire regular & forced remainder steps
on the Histories rate: use e.g. seed=lead=0. Unlike E's further estimates,
`AtomStep` doesn't need a separate *coupling*-small coordinate error once
receiving this small a. -/
theorem paid_via_tare (S : Slots (Cur).activities (fun i => joint B 0 (X i))) (h : H.Conv N p j)
    (hr : Readable A B (Cur).p (H.S.side j p) w) (hf : M.Format 0 X Cur)
    (he : M.eval 0 X B Cur = blast H N p j d g)
    (hx : Tare M 0 X A B Cur w Scale (kappa H j) a b c)
    (h₁ : orbitCost F*(F.coeffSize (M.seed-lead)+a) ≤ q) (h₂ : turnCost (Cur).p.order (Cur).p.power*a+(b+c) ≤ r) :
    PaidAtom B H N p j A g lead q r := by
  have hk := Real.sqrt_pos.mpr (forcedPos H.levels j)
  have hd := (Raw.build_density S h.good hr hf (hx.income hk le_rfl) hk).trans he
  apply paid_center (fun s => h.good.labels.moves s 0) hr.sound (Raw.build_format S h.good.labels.forced hr hf) hd
    (hx.tab S hk h.good.labels.boundK hr hf) _ h₂
  exact (mul_le_mul_of_nonneg_left (hx.canonical_cost S hr hf lead) (zero_le_one.trans (orbitCost_one_le F))).trans h₁

end block
end YM.Planned.GuardedAtom
