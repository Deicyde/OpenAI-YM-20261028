import YM.Push.LOCAL_SPLITTING.Funding



/-!
# A single distinguished gas component (unforced OR forced)

Use the SAME alphabet on all of `Rep`. If the flag inventory is empty, turn this component
into a raw regular multiplier and **subtract** a meeting correction involving all nonempty
bundles of actual overlapping vacuum factors. If the inventory is nonempty, use a
pre-booked gas address with the actual mask. Coordinate extraction and moving regular
good masks (E eq:Jmdef) will involve still other corrections, for which `Raw.build` can
use the same reserve. No injectivity across these several operations required at singleton
order, but injectivity WITHIN each address booking is proved. No use of junk `tsum`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Function Filter Lattice Wilson RG Source MeasureTheory Push.Local Labels
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical

/-- Unmasked component payload with complete output support. Masks imposed by `seen`.
On forced components, further internal predicates go inside val. -/
structure Letter (G : Gauge) (n : Side) where
  support : Support n
  inventory : Support n
  val : Config G n → ℂ

variable {G : Gauge} {n : Side}

namespace Letter
variable (L : Letter G n) (B : BudgetPoint)

def Guard (V : Config G n) := L.support ∩ flags B.threshold V = L.inventory

def seen (V : Config G n) := if L.Guard B V then L.val V else 0





/-- Regularity *before* mask on components with empty inventory, as required. -/
structure Shape (o : Site n) : Prop where
  anchor : o ∈ L.support
  kept : L.inventory ⊆ L.support
  borel : Measurable L.val
  final_reads : UsesFinal B.threshold L.support L.val
  invariant : GaugeInvariant L.val
  bulk : L.inventory = ∅ → B.Regular L.support L.val

variable {L B}

lemma guard_meas : MeasurableSet {V | L.Guard B V} := by
  rw [show {V | L.Guard B V} = ⋃ X : {X : Support n // L.support ∩ X = L.inventory},
      {V | flags B.threshold V = X.val} by
    ext V; simp only [Set.mem_setOf_eq,Set.mem_iUnion]; exact ⟨fun h => ⟨⟨_,h⟩,rfl⟩,fun ⟨X,hX⟩ => show _ ∩ _ = L.inventory from hX.symm ▸ X.property⟩]
  exact MeasurableSet.iUnion fun _ => flags_measurable_eq ..

lemma Shape.measurable {o : Site n} (h : L.Shape B o) : Measurable (L.seen B) := Measurable.ite guard_meas h.borel measurable_const

lemma Shape.uses {o : Site n} (h : L.Shape B o) : UsesFinal B.threshold L.support (L.seen B) := by
  intro U V he hf; unfold seen Guard; rw [hf,h.final_reads U V he hf]



/-- `price` applies on the guarded domain at value order, and for unforced
components through `B.order` on their good domain. -/
structure Bound (L : Letter G n) (B : BudgetPoint) (o : Site n) (c : ℝ) : Prop where
  nonneg : 0 ≤ c
  covers (V : Config G n) : L.Guard B V → ‖L.val V‖ ≤ c
  bulk : L.inventory = ∅ → B.supBounds o L.support L.val c

lemma Bound.pays {o : Site n} {c : ℝ} (h : L.Bound B o c) (V : Config G n) : ‖L.seen B V‖ ≤ c := by
  unfold seen; split
  · rename_i he; exact h.covers _ he
  exact norm_zero.trans_le h.nonneg

def barePart (L : Letter G n) := if L.inventory.Nonempty then (0 : Config G n → ℂ) else L.val



def goodPart (L : Letter G n) (B : BudgetPoint) := masked B.threshold L.support L.barePart





theorem Bound.bare {o c} (h : L.Bound B o c) : B.supBounds o L.support L.barePart c := by
  unfold barePart; split
  · exact bound_weaken (bound_const _) (norm_zero.trans_le h.nonneg)
  next hN => exact h.bulk (Finset.not_nonempty_iff_eq_empty.mp hN)

theorem Bound.good {o c} (h : L.Bound B o c) (U : Config G n) : ‖L.goodPart B U‖ ≤ c := by
  unfold goodPart; by_cases ht : Healthy B.threshold L.support U
  · rw [masked_eq _ _ _ _ ht]; exact h.bare.2 U ht [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ ht]; exact norm_zero.trans_le h.nonneg

def blank (G : Gauge) (o : Site n) : Letter G n := ⟨{o},∅,0⟩

@[simp] lemma blank_seen (G : Gauge) (o : Site n) (B : BudgetPoint) (V) : (blank G o).seen B V = 0 := by simp [seen,blank]





end Letter

namespace Assembly
variable {ι : Type*} {d : ℕ} {F : Labels.Frame G d} (E : ι ↪ ℕ) (L : ι → Letter G n) (o : Site n) (B : BudgetPoint) (R : Rep G n)

/-- Extend unmasked *gas components*, before applying the coefficient conversion. -/
def pad : ℕ → Letter G n := extend E L (fun _ => Letter.blank G o)

@[simp] theorem padded (i : ι) : pad E L o (E i) = L i := E.injective.extend_apply ..











end Assembly

namespace Spool
variable {n : Side} {G : Gauge} {d : ℕ} {F : Labels.Frame G d}
  {L : ℕ → Letter G n} {R : Rep G n}

abbrev Hard (L : ℕ → Letter G n) := {i // (L i).inventory.Nonempty}

/-- Enough addresses for the distinguished nonempty-inventory components.
With true inventory tests (additional tests can be included inside the component). -/
structure Board (L : ℕ → Letter G n) (R : Rep G n) where
  cell : Hard L ↪ ℕ
  sites (i) : (R.activities.forced (cell i)).support = (L i.val).support
  inventory (i) : (R.activities.forced (cell i)).inventory = (L i.val).inventory
  allows (i) (U : Config G n) : (R.activities.forced (cell i)).extraTest U



variable (S : Board L R)

def issued := extend S.cell (fun i => (L i.val).seen R.p) (0 : ℕ → Config G n → ℂ)

lemma issued_cell (i) : issued S (S.cell i) = (L i.val).seen R.p := S.cell.injective.extend_apply ..
lemma issued_blank {i} (hi : ¬ ∃ j,S.cell j=i) : issued S i=0 := extend_apply' _ _ _ hi



lemma issued_cost {o : Site n} {e : ℕ → ℝ} (h : ∀ i,(L i).Bound R.p o (e i)) {C : ℝ}
    (he : SumBudget (fun i => R.p.mass (L i).support (e i)) C) : ForceCost R.p R.activities (issued S) C := by
  let b := extend S.cell (fun i => e i.val) (0 : ℕ → ℝ)
  have hsub := sumBudget_subtype (fun i => (L i).inventory.Nonempty) he
  refine ⟨b,sumBudget_pass S.cell _ (by simpa only [S.cell.injective.extend_apply,b, Push.Local.patch, S.sites] using! hsub) ?_,fun i => ?_⟩
  · intro i hi; rw [show b i = 0 from extend_apply' _ _ _ hi,BudgetPoint.mass,mul_zero]
  by_cases hi : ∃ j,S.cell j=i
  · obtain ⟨j,rfl⟩ := hi; rw [issued_cell, show b _ = _ from S.cell.injective.extend_apply ..]
    exact ⟨(h _).nonneg,(h _).pays⟩
  rw [issued_blank S hi,show b i=0 from extend_apply' _ _ _ hi]; simp





variable (F) in
def raw (s : Slots R.activities (fun i => (L i).support)) : Raw F n where
  seed := 0
  bulk i := (L i).barePart
  forced := issued S + s.packLinear R.p.threshold (-(fun i => (L i).goodPart R.p))

variable (s : Slots R.activities (fun i => (L i).support))



lemma rem_bound {o : Site n} {e : ℕ → ℝ} {C v : ℝ} (hv : 0 ≤ v) (hR : R.activities.KBound R.p v)
    (hh : hitWidth R.p * Real.sqrt v ≤ 1) (h : ∀ i,(L i).Bound R.p o (e i))
    (he : SumBudget (fun i => reservedMass R.p (L i).support (e i)) C) :
    ForceCost R.p R.activities (issued S) C ∧ ForceCost R.p R.activities (s.packLinear R.p.threshold
      (-(fun i => (L i).goodPart R.p))) C := by
  have hm (i) := (h i).nonneg
  have hr := width_one_le R.p
  have hu : hitWidth R.p * v ≤ 1 := calc
    _ ≤ hitWidth R.p * (hitWidth R.p * v) := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hv hr) (by positivity)
    _ = (hitWidth R.p * Real.sqrt v) ^ 2 := by rw [mul_pow,Real.sq_sqrt hv]; ring
    _ ≤ 1 := pow_le_one₀ (by positivity) hh
  refine ⟨issued_cost S h (sumBudget_mono he (fun i => mul_nonneg (Real.exp_pos _).le (hm i)) (fun i => ?_) le_rfl),
    s.forceCost hR (sumBudget_mono he (fun i => mergePrice_nonneg _ _ hv (hm i)) (fun i => (price_meeting hv hu (hm i) _).trans (mul_le_of_le_one_left (mul_nonneg (Real.exp_pos _).le (hm i)) hu)) le_rfl) hm (fun i U => ?_)⟩
  · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (by positivity))) (hm i)
  simpa using (h i).good U

lemma income {o : Site n} {e : ℕ → ℝ} {C v w paid : ℝ} {A : Hol G} {T : SectionData F}
    (hv : 0 < v) (hR : R.activities.KBound R.p v) (ht : T.Sound A) (hw : 0 ≤ w)
    (hh : hitWidth R.p * Real.sqrt v ≤ 1) (hs : ∀ i,(L i).Shape R.p o) (h : ∀ i,(L i).Bound R.p o (e i))
    (he : SumBudget (fun i => reservedMass R.p (L i).support (e i)) C)
    (hk : (2*factor A T R.p.supportExponent w+2)*(C/Real.sqrt v) ≤ paid) :
    (raw F S s).Income o (fun i => (L i).support) A T R w v (Real.sqrt v) paid := by
  have hf := zero_le_one.trans (atomPrice_ge_one A F hw)
  have h₁ : 0 ≤ factor A T R.p.supportExponent w := mul_nonneg (Real.exp_pos _).le hf
  have h₂ : 0 ≤ C := (tsum_nonneg he.1).trans he.2.2
  have hp : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hκ' : Real.sqrt v ≤ 1 := (le_mul_of_one_le_left hp.le (width_one_le _)).trans hh
  obtain ⟨hr₁,hr₂⟩ := rem_bound S s hv.le hR hh h he
  have hc : C ≤ C / Real.sqrt v := (le_div_iff₀ hp).mpr (mul_le_of_le_one_right h₂ hκ')
  refine income_of_reserved ht (fun i => (hs i).anchor) (fun i => (h i).bare) he (b:=(C+C)/Real.sqrt v)
      (by rw [mul_div_cancel₀ _ hp.ne']; exact hr₁.add hr₂) h₂ (by positivity) hv.le hw hh ((add_le_add_left (mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2*factor A T R.p.supportExponent w)) _).trans ?_)

  rw [add_div]; linarith




end Spool
end YM.Planned.Forced
