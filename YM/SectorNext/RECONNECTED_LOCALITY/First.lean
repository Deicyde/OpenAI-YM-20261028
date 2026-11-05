import YM.SectorNext.RECONNECTED_LOCALITY.Marginals
import YM.SectorNext.RECONNECTED_LOCALITY.Pinned


set_option warningAsError false

/-!
# Paying and reassembling the first gas expectation

Once a transformed step has been written on this IR in the chargeable regime (and with
all queries bought) this file proves the rearrangement to local gas coefficients and the
volume-independent exponential real budgets, including the extra compulsory seed gain.

The
source ties to specific `Allocation.bill` terms multiplied by `R.eval` and integrates on
the ACTUAL F before calling this service (see subsequent files).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect
open RG Lattice Filter Function MeasureTheory Words Wilson Window Bind
open scoped Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c : Side} {ι η κ : Type*} {Y : η → Type*}
variable [∀ i,MeasurableSpace (Y i)]
variable [Fintype κ] [Fintype η] (P : BudgetPoint) (X : Form G c ι κ Y)

namespace Form



def component (N : StageLaw G c ι κ Y) (m : ∀ i,Measure (Y i)) (ρ : ℝ → ℝ)
    (V : Config G c) : Finset ι → ℝ := clause X.gate X.foot X.flag (flags P.threshold V) fun p =>
      if Ac.Spark X.foot p then X.edition N m p p V ρ else 0

end Form
variable {X P}
variable {N : StageLaw G c ι κ Y} {m : ∀ i, Measure (Y i)}
variable [∀ i,IsProbabilityMeasure (m i)]

/-- Input analytic estimate, deliberately on *actual* joint integrals. Need neither moments
nor factorization assumptions on the disconnected terms. Needed on every individually chargeable
component, even before determining whether it will be globally used after assembling. Here a
simple regime with one compulsory mark payment whenever any OUTPUT flag address is present.
Use e.g. $w=\exp(-c_L p_*^2)$, showing one activated energy packet will give it via its actual
differentiated or undifferentiated integral estimate. Arguably simpler and stronger than some E
budgets: may increase `f` for any vertex to cover its variants (but still must pay hit). For a
more flexible price spelling with shared trigger events see later. Poly occurrence loss `r`
can be as large as needed *if* reserving the same before L. `f` evaluated on the actual address
variants; cannot charge one gain many times by using an address just for the parent.
-/
structure Pulse (X : Form G c ι κ Y) (N : StageLaw G c ι κ Y) (P : BudgetPoint) (m : ∀ i, Measure (Y i))
    (f : ι → ℝ) (d w r : ℝ) : Prop where
  loss : 0 ≤ r
  cost : 0 ≤ d
  bonus : w ∈ Set.Icc 0 1
  active : ∀ (p : Finset ι) (V : Config G c), Ac.Spark X.foot p → X.Ok p → X.Reads P p V →
    (∀ t,Integrable (X.roll p p V t) (N.map p V t)) ∧
      Integrable (X.booth N p p V abs) (Measure.pi m)
  price : ∀ p V, Ac.Spark X.foot p → X.Ok p → X.Reads P p V →
    X.edition N m p p V abs ≤ (d*(if (X.vote p).Nonempty then w else 1))*
      Real.exp (r*Ledger.occurred X.foot P.B p) * ∏ i∈p,f i

namespace Form
variable (P X)

def provision (f : ι → ℝ) (d w r : ℝ) (p : Finset ι) :=
    if Ac.Spark X.foot p then (d*(if (X.vote p).Nonempty then w else 1))*
      Real.exp (r*Ledger.occurred X.foot P.B p) * ∏ i∈p,f i else 0

variable {P X} {f : ι → ℝ} {d w r γ a : ℝ} (hL : Ledger.Takes X.foot P.B f (a+r) γ) (ha : 0 ≤ a)

omit [∀ i,MeasurableSpace (Y i)] [Fintype κ] [Fintype η] in
lemma provided (p : Finset ι) (hb : 0 ≤ w) (hv : 0 ≤ d) (he : ∀ i,0 ≤ f i) : 0 ≤ provision P X f d w r p := by
  unfold provision; split
  · refine mul_nonneg (mul_nonneg (mul_nonneg hv ?_) (Real.exp_nonneg _)) (Finset.prod_nonneg fun _ _ => he _)
    split <;> first | exact hb | exact zero_le_one
  exact le_rfl

include hL ha
omit [Fintype κ] [∀ i,IsProbabilityMeasure (m i)] in
/-- The weight paid on complete output supports at THIS radius & reserve,
with the occupancy gain reusable for forced outputs. -/
theorem submitted (h : Pulse X N P m f d w r) :
    Ac.Hit X.land P.B (provision P X f d w r) a (d*(Real.exp γ-1)) ∧
      Ac.Hit X.land P.B (fun p => if (X.vote p).Nonempty then provision P X f d w r p else 0) a
        ((d*w)*(Real.exp γ-1)) := by
  have he (p : Finset ι) : 0 ≤ provision P X f d w r p := provided p h.bonus.1 h.cost hL.pos
  constructor
  · refine Ledger.pays_enlargement (fun _ => Finset.Subset.refl _) hL ha h.loss he
      (fun s hn => of_not_not (fun hh => hn (if_neg hh))) _ h.cost ?_
    intro s hs; unfold provision
    rw [if_pos hs]; split
    · gcongr; any_goals exact Finset.prod_nonneg fun _ _ => hL.pos _
      exact mul_le_of_le_one_right h.cost h.bonus.2
    rw [mul_one]
  refine Ledger.pays_enlargement (fun _ => Finset.Subset.refl _) hL ha h.loss (fun p => ?_)
    (fun p hn => of_not_not fun ht => hn ?_) _ (mul_nonneg h.cost h.bonus.1) ?_
  · split
    · exact he _
    exact le_rfl
  · split
    · exact if_neg ht
    rfl
  intro s hs; simp only [provision,hs,↓reduceIte]; split_ifs
  · exact le_rfl
  exact mul_nonneg (mul_nonneg (mul_nonneg h.cost h.bonus.1) (Real.exp_nonneg _))
    (Finset.prod_nonneg fun _ _ => hL.pos _)

end Form

namespace Pulse
variable {f : ι → ℝ} {d w r : ℝ} (h : Pulse X N P m f d w r) (H : Cellular X N)
variable (L : Printed X N)
include L H h

omit [∀ i, IsProbabilityMeasure (m i)] in
lemma still_active (V : Config G c) (p : Finset ι) {ρ : ℝ → ℝ} (hρ : Measurable ρ)
    (hm : ∀ x,‖ρ x‖ ≤ ‖x‖) (he : Ac.Spark X.foot p) (hv : X.Ok p) (hr : X.Reads P p V) :
    (∀ t, Integrable (fun z => ρ (X.roll p p V t z)) (N.map p V t)) ∧
      Integrable (X.booth N p p V ρ) (Measure.pi m) := by
  have hi := h.active p V he hv hr
  have ha : Measurable (X.booth N p p V ρ) := (Cellular.booth_joint H L p p ρ hρ).comp (measurable_prodMk_left (x:=V))
  refine ⟨fun t => (hi.1 t).mono (Cellular.at_time L _ _ _ t hρ).aestronglyMeasurable (Eventually.of_forall fun z => hm _),
    hi.2.mono ha.aestronglyMeasurable (Eventually.of_forall fun x => ?_)⟩
  simp only [Form.booth, Real.norm_of_nonneg (integral_nonneg (f:=fun z => |X.roll p p V x z|) fun _ => abs_nonneg _)]
  apply norm_integral_le_of_norm_le (by simpa only [Real.norm_eq_abs] using (hi.1 x).norm)
  exact Eventually.of_forall fun _ => hm _

omit [∀ i, IsProbabilityMeasure (m i)] [Fintype κ] H L in
lemma price_charge {a γ : ℝ} (hL : Ledger.Takes X.foot P.B f (a+r) γ) (V : Config G c) (p : Finset ι)
    {ρ : ℝ → ℝ} (hm : ∀ x, ‖ρ x‖ ≤ ‖x‖) :
    ‖X.component P N m ρ V p‖ ≤ X.provision P f d w r p := by
  unfold Form.component clause
  simp only
  by_cases he : Ac.Spark X.foot p
  · rw [if_pos he]; split
    · rename_i hh
      apply le_trans ?_ (le_trans (h.price p V he hh.1 hh.2) (le_of_eq (if_pos he).symm))
      unfold Form.edition
      have hn:=h.active p V he hh.1 hh.2
      refine norm_integral_le_of_norm_le hn.2 (Eventually.of_forall fun t => ?_)
      exact norm_integral_le_of_norm_le (by simpa only [Real.norm_eq_abs] using (hn.1 t).norm) (Eventually.of_forall fun _ => hm _)
    rw [norm_zero]; exact Form.provided p h.bonus.1 h.cost hL.pos
  rw [if_neg he, Form.provision, if_neg he]; split_ifs <;> simp







end Pulse

namespace Form

variable (N : StageLaw G c ι κ Y) (m : ∀ i,Measure (Y i))



-- supply transport hypothesis in a separate service
structure Dossier (p : Finset ι) (D : ℝ) : Prop where
  lookup : LocalOn (X.land p) (fun V => X.edition N m p p V id)
  after : UsesFinal P.threshold (X.land p) (fun V => X.component P N m id V p)
  inStep : LocalOn (inspected (X.land p)) (fun V => X.component P N m id V p)
  printed : Measurable (fun V => X.component P N m id V p)
  amount : ∀ V, ‖X.component P N m id V p‖ ≤ D



end Form
end YM.SectorNext.Reconnect
