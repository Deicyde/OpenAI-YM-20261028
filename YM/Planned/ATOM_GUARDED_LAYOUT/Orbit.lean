import YM.Extra.SOURCE_HISTORIES.LocalDebt
import YM.Push.LOCAL_SPLITTING.Transport


/-!
# Atom socket: orbit of ONE split presentation

Produce the orbit required by `PaidAtom` from an unrotated split on the
same vacuum. Use the given `Moves` rather than assuming the forced
coefficients can be interpreted with a new set of masks. Includes
ordinary conjugation of the FULL insertion (as opposed e.g. to just
conjugating the canonical-insertion coefficients). No nonwrapping
hypothesis. The side-size guard when actually using `reorient` here
comes from the schedule in applications. Prices are for the actual
ordered-LEFT-derivative norm, not just for identity jets.
-/
set_option autoImplicit false
noncomputable section

namespace YM.Planned.GuardedAtom
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Bid Push.Local Next.Foundations Extra.Histories
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

/-- Ordinary conjugation commutes even with the equality case of Healthy. -/
theorem masked_bar (t : ℝ) (X : Support n) (f : Config G n → ℂ) (U : Config G n) :
    masked t X (star f) U = star (masked t X f U) := by
  by_cases h : Healthy t X U <;> simp [h]

/-- Bar the *entire* coefficient in place. No permutation of activities
necessary, since vacuum coefficients use real conventions. -/
def barAll (P : Coefficient F n) : Coefficient F n where
  x := star P.x
  support := P.support
  regular i := star (P.regular i)
  forced i := star (P.forced i)

variable {P : Coefficient F n} {R : Rep G n} {o : Site n} {A : Hol G} {B : SectionData F}

theorem format_barAll (h : P.Format o A R) : (barAll P).Format o A R := by
  have he (i : ℕ) := reads_bar ((reads_null_iff A d ..).mpr ⟨h.identity_null i, h.projects i⟩)
  rw [show Labels.realBar (0 : Label G d) = 0 from map_zero _] at he  -- realBar p not a motion warp
  refine ⟨fun i => regular_bar (h.smooth i),h.origin,fun i => ((reads_null_iff ..).mp (he i)).1,
    fun i => ((reads_null_iff ..).mp (he i)).2, fun i U hi => ?_,fun i hi => ?_,
    fun i g U => congr_arg star (h.invariant i g U),fun i U V H hflag => congr_arg star (h.supported i U V H hflag), ?_⟩
  · exact h.forcing i U (fun H => hi (by simp [barAll,H]))
  · exact h.carried i (fun H => hi (by simp [barAll,H]))
  intro i
  exact (continuous_star.measurable.comp (h.borel i) : Measurable (fun U : Config G n => star (P.forced i U)))

theorem density_barAll (P : Coefficient F n) (h : B.Sound A) :
    (barAll P).density o B R = star (P.density o B R) := by
  have hb (i) (U : Config G n) : (barAll P).maskedTerm R i U = star (P.maskedTerm R i U) :=
    masked_bar ..
  have hY U : (barAll P).exponentialEntry o B R U = star (P.exponentialEntry o B R U) := by
    rw [Coefficient.exponentialEntry,Coefficient.exponentialEntry, star_add,star_add,tsum_star]
    simp_rw [hb,barAll,Pi.star_apply]
    rw [core_star,scaled_star,show B.places (star (F.scaled R.p.threshold⁻¹ (F.core P.x))) o = star (B.places (F.scaled R.p.threshold⁻¹ (F.core P.x)) o) from funext fun _ => h.ordinary_real ..,masked_bar]
  have hm (i) (U : Config G n) : (barAll P).marked R i U = star (P.marked R i U) := by
    unfold Coefficient.marked; split
    · simp [barAll,star_sum,star_mul',star_prod]
    exact (star_zero ℂ).symm
  funext U
  simp only [Coefficient.density, Pi.star_apply, hY, hm, star_add, star_mul', tsum_star]
  have hv (x : ℝ) : star (x : ℂ) = x := by simp
  rw [hv (R.eval U), hv (Real.exp (R.exponent U))]

/-- Display the two pieces of the remainder cost separately. This is
`remBound` before taking the sum (equivalence below). In particular a budget
on the forced address is a budget on the same support and inventory; it
is not made relative to the value of the unmarked density. -/
structure Tab (P : Coefficient F n) (o : Site n) (R : Rep G n) (κ a b : ℝ) : Prop where
  divisor : 0 < κ
  first : 0 ≤ a
  second : 0 ≤ b
  regular : ∃ e : ℕ → ℝ, SumBudget (fun i => R.p.mass (P.support i) (e i)) a ∧
    ∀ i, R.p.supBounds o (P.support i) (P.regular i) (e i)
  forced : ForceCost R.p R.activities P.forced (κ*b)

variable {κ a b c : ℝ}

theorem rem_tabs : P.remBound o R κ c ↔ ∃ a b : ℝ, Tab P o R κ a b ∧ a+b ≤ c := by
  constructor
  · rintro ⟨a,b,h1,h2,h3,h4,h5,h6⟩
    exact ⟨a,b,⟨h4,h1,h2,h5,h6⟩,h3⟩
  rintro ⟨a,b,⟨h4,h1,h2,h5,h6⟩,h3⟩
  exact ⟨a,b,h1,h2,h3,h4,h5,h6⟩

lemma Tab.bound (h : Tab P o R κ a b) (hc : a+b ≤ c) : P.remBound o R κ c :=
  rem_tabs.mpr ⟨a,b,h,hc⟩

lemma Tab.bar (h : Tab P o R κ a b) (hf : P.Format o A R) : Tab (barAll P) o R κ a b := by
  obtain ⟨e,hE,hB⟩ := h.regular
  obtain ⟨u,hU,hD⟩ := h.forced
  exact ⟨h.divisor,h.first,h.second,⟨e,hE,fun i => bound_bar (hf.smooth i) (hB i)⟩,
    u,hU,fun i => ⟨(hD i).1, fun U => (norm_star (P.forced i U)).trans_le ((hD i).2 U)⟩⟩

variable {s : Signed} {y : Site n} (m : R.activities.Moves s y)

/-- Pull cost *only* on regular part (no derivative on the forced reads).
Cf `cap_reorient`; keeping the Tab here allows slack IF the output producer
has separate bills. -/
lemma Tab.turn (h : Tab P o R κ a b) (hf : P.Format o A R) :
    Tab (reorient m P) (affine s y o) R κ (turnCost R.p.order R.p.power*a) b := by
  let t := turnCost R.p.order R.p.power
  have ht : 0 ≤ t := pow_nonneg (by positivity) _
  let r := turnSites s y
  have hm (Z : Support n) (v : ℝ) : R.p.mass (Z.image r) v = R.p.mass Z v := by unfold BudgetPoint.mass; rw [cover_map r (turn_sep s y)]
  obtain ⟨v,hx,hy⟩ := h.regular
  obtain ⟨w,hz,hw⟩ := h.forced
  refine ⟨h.divisor,mul_nonneg ht h.first,h.second,⟨fun i => t*v i,?_,fun i => bound_pull (hf.smooth i) (hy i) s y⟩,
    ⟨fun i => w (m.kp.symm i),sumBudget_pass m.kp.toEmbedding _ ?_ (fun i hi => absurd (m.kp.surjective i) hi),
      fun i => ⟨(hw _).1, fun U => (hw _).2 (pull s y U)⟩⟩⟩
  · simpa only [t,reorient,BudgetPoint.mass,cover_map _ (turn_sep s y),mul_left_comm _ (turnCost R.p.order R.p.power)] using sumBudget_mul_left hx ht
  simpa only [patch,Equiv.coe_toEmbedding,m.forced_support,m.kp.symm_apply_apply,show affine s y=⇑r from rfl,hm] using! hz

open Motion

lemma patch_sub (z : Extra.Histories.Motion) (f g : F.Coeff) : Motion.patch F z (f-g) = Motion.patch F z f-Motion.patch F z g := by
  unfold Motion.patch; split <;> simp

/-- Change the WHOLE presentation, with precisely the supplied orientation
on the actual labels. Anchor and section are the same. -/
def audition {z : Extra.Histories.Motion} (S : R.activities.Moves z.1 y) (P : Coefficient F n) : Coefficient F n :=
  if z.2 then barAll (reorient S P) else reorient S P

variable (z : Extra.Histories.Motion) (S : R.activities.Moves z.1 0)

lemma audition_receipt (hn : 2 ≤ n.val) (ht : B.Sound A) (hf : P.Format 0 A R) (h : Tab P 0 R κ a b) :
    (audition S P).x=Motion.patch F z P.x ∧ (audition S P).Format (0:Site n) A R ∧
    Tab (audition S P) (0:Site n) R κ (turnCost R.p.order R.p.power*a) b ∧
      (audition S P).density 0 B R = dance z (P.density 0 B R) := by
  have HX : affine z.1 (0:Site n) 0 = 0 := by simp [affine]
  have he := format_reorient S hf hn
  have hy := Tab.turn S h hf
  have hz := density_reorient (o:=(0:Site n)) S ht P
  rw [HX] at he hy hz
  unfold audition
  unfold Motion.patch
  unfold dance scalar
  cases z.2 with
  | false => exact ⟨rfl,he,hy,hz⟩
  | true => exact ⟨rfl,format_barAll he,hy.bar he, (density_barAll _ ht).trans (congr_arg star hz)⟩

variable {H : History G} {N p j : ℕ} {X : Config G (H.S.side (j+1) p) → ℂ} {lead : F.Coeff}
variable {Q : Coefficient F (H.S.side j p)}

/-- A split at the center suffices; no assumptions at *any* other Motion
(and no action on the fine-side hypotheses, branch, normalization etc.
needed). Orbit costs for direction and regular jets are displayed. -/
theorem paid_center (hm : ∀ s : Signed, Nonempty ((H.rep N p j).activities.Moves s 0))
    (ht : B.Sound A) (hf : Q.Format 0 A (H.rep N p j))
    (he : Q.density 0 B (H.rep N p j) = blast H N p j d X)
    (h : Tab Q 0 (H.rep N p j) (Real.sqrt (H.levels.clock.forcedAllowance j)) a b)
    (hc : orbitCost F * F.coeffSize (Q.x-lead) ≤ c) {w : ℝ}
    (hr : turnCost (H.rep N p j).p.order (H.rep N p j).p.power*a + b ≤ w) :
    PaidAtom B H N p j A X lead c w := by
  refine ⟨Q.x, fun z => ?_⟩
  let S := Classical.choice (hm z.1)
  obtain ⟨hx,ht,hb,hD⟩ := audition_receipt z S ((by decide : 2 ≤ 4).trans (actual_side_ge H.S j p)) ht hf h
  exact ⟨(patch_sub (F:=F) z Q.x lead).symm ▸ ((patch_cost F z (Q.x-lead)).trans hc),
    audition S Q,hx,ht,hb.bound hr,hD.trans (congr_arg (dance z) he)⟩

end YM.Planned.GuardedAtom
