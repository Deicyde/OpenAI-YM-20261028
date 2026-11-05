import YM.Next.BOUNDARY.Alias
import YM.PREC.Derivative
import YM.Push.SECTOR_MEASURE.Cells
import YM.Work.B04
-- smooth one-dimensional profiles


/-!
# The two allocations of sector costs

Includes the partition of unity version literally (in the
1/4 convention); this is *not* a partition by disjoint supports.
Numerical weights move across the overlap band, testing all physical
sites/bonds. These results are real and Borel; don't assert that V reads
through a branch switch, flags, masks etc. smoothly.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.SectorMeasure

open Lattice RG Wilson Pressure MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x W : ℝ}

/-- A partition of unity subordinate to the seed prerequisites.
The data themselves do **not** include likelihood; their physical support
with positive likelihood will be in the Plot. -/
structure Allocation (G : Gauge) (S : StepData c f) (x W : ℝ) where
  bill : Stores S → S.Choices → Config G f → Config G c → ℝ
  nonneg A k U V : 0 ≤ bill A k U V
  sums k U V : ∑ A, bill A k U V = 1
  borel : S.patch.Branches S.kernel G → ∀ A k,
    Measurable (fun r : Config G f × Config G c => bill A k r.1 r.2)
  actual : ∀ A k U V, bill A k U V ≠ 0 → Seeded A U k V x W

namespace Allocation
variable (D : Allocation G S x W)

theorem range (A : Stores S) (k : S.Choices) (U : Config G f) (V : Config G c) : D.bill A k U V ≤ 1 := by
  rw [← D.sums k U V]
  exact Finset.single_le_sum (fun B _ => D.nonneg B k U V) (Finset.mem_univ A)

theorem envelope {α : Type*} [MeasurableSpace α] {U : α → Config G f} {V : α → Config G c}
    (h : S.patch.Branches S.kernel G) (u : Measurable U) (v : Measurable V) (A : Stores S) (k : S.Choices) :
    Envelope (fun a => D.bill A k (U a) (V a)) :=
  ⟨(D.borel h A k).comp (u.prodMk v),1,fun _ => (Real.norm_of_nonneg (D.nonneg ..)).trans_le (D.range ..)⟩

theorem plots {A : Stores S} {k : S.Choices} {U : Config G f} {V : Config G c}
    (h : D.bill A k U V ≠ 0) (l : Alive S U k) : Stores.Plot A U k V x W := (D.actual _ _ _ _ h).plot l

/-- 's incidence (intact global sector). Every actual fine flag
requires a nondefault fine plaquette, independent of what is booked in
the overlap band. -/
theorem flagged {A : Stores S} {k : S.Choices} {U : Config G f} {V : Config G c}
    (h : D.bill A k U V ≠ 0) (i : Site f) (hi : i ∈ RG.flags (fiery G x S.patch.L) U) :
    ∃ p ∈ A.costs, i ∈ RG.touched p := by
  obtain ⟨p,hp,hr⟩ := (RG.flags_spec ..).1 hi
  refine ⟨p,?_,hp⟩
  by_contra hv
  have hm := ((D.actual _ _ _ _ h).fine p).2 hv
  change fiery _ _ _ < toll U p at hr
  have ht : 0 ≤ fiery G x S.patch.L := temp_nonneg _
  linarith

/-- The disjoint hard allocation; also valid in degenerate cases. -/
def hard (G : Gauge) (S : StepData c f) (x W : ℝ) : Allocation G S x W where
  bill A k U V := if booking S x W U k V = A then 1 else 0
  nonneg := by intros; split <;> norm_num
  sums := by intros; simp
  borel h A k := Measurable.ite (booking_meas k x W A h measurable_fst measurable_snd)
    measurable_const measurable_const
  actual := by
    intro A k U V h
    split at h
    next e => rw [← e]; exact booking_seeded U k V x W
    next _ => exact False.elim (h rfl)

end Allocation

/-- E χ, extended to ℝ (only evaluated on squares). Use a genuine
smooth cutoff here even though the finite-measure lemmas need only
bounded Borel and the displayed support guards. -/
structure Chi where
  read : ℝ → ℝ
  range y : read y ∈ Set.Icc 0 1
  to_one : ∀ y, y ≤ 1 → read y = 1
  to_zero : ∀ y, 4 ≤ y → read y = 0
  smooth : ContDiff ℝ ∞ read
  mono : Antitone read

namespace Chi

def canonical : Chi where
  read y := Real.smoothTransition ((4-y)/3)
  range _ := ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  to_one _ h := Real.smoothTransition.one_of_one_le (by linarith)
  to_zero _ h := Real.smoothTransition.zero_of_nonpos (by linarith)
  smooth := Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)
  mono := fun _ _ h => Real.smoothTransition.monotone (by linarith)

variable (q : Chi)

/-- Default in cutoff units with denominator `d`. -/
def innerShare (d r : ℝ) := q.read ((r/d)^2)

theorem chosen_lt (r d : ℝ) (hd : 0 < d) (h : q.innerShare d r ≠ 0) : r < 2*d := by
  by_contra! e
  have he : 2 ≤ r/d := (le_div_iff₀ hd).2 e
  exact h (q.to_zero _ (by nlinarith))

theorem exterior_gt (r d : ℝ) (hr : 0 ≤ r) (hd : 0 < d) (h : 1 - q.innerShare d r ≠ 0) : d < r := by
  by_contra! e
  have he : r/d ≤ 1 := (div_le_one hd).2 e
  have hh : 0 ≤ r/d := by positivity
  have hg : q.innerShare d r = 1 := q.to_one _ (by nlinarith)
  exact h (by rw [hg, sub_self])

section table

variable {ι α : Type*} [Fintype ι] [DecidableEq ι]

/-- Every input physical address carries one of two complementary
weights. -/
def share (s : Finset ι) (r : ι → ℝ) (d : ℝ) : ℝ :=
  (∏ i ∈ s, (1 - q.innerShare d (r i))) * ∏ i ∈ sᶜ, q.innerShare d (r i)

theorem share_nonneg (s : Finset ι) (r : ι → ℝ) (d : ℝ) : 0 ≤ q.share s r d :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => sub_nonneg.mpr (q.range _).2)
    (Finset.prod_nonneg fun _ _ => (q.range _).1)

theorem share_sum (r : ι → ℝ) (d : ℝ) : ∑ s, q.share s r d = 1 := by
  unfold share
  rw [← Fintype.prod_add]
  simp

theorem share_meas [MeasurableSpace α] (s : Finset ι) (r : α → ι → ℝ)
    (h : ∀ i, Measurable (fun a => r a i)) (d : ℝ) : Measurable (fun a => q.share s (r a) d) := by
  have he (i : ι) : Measurable (fun a => q.innerShare d (r a i)) :=
    q.smooth.continuous.measurable.comp (((h i).div_const d).pow_const 2)
  exact ((Finset.measurable_fun_prod _ fun i _ => measurable_const.sub (he i)).mul
    (Finset.measurable_fun_prod _ fun i _ => he i))

theorem share_cuts (s : Finset ι) (r : ι → ℝ) (d : ℝ) (h : q.share s r d ≠ 0)
    (hd : 0 < d) (i : ι) (hr : 0 ≤ r i) :
    (i ∈ s → d < r i) ∧ (i ∉ s → r i < 2*d) := by
  constructor
  · intro hi
    apply q.exterior_gt _ _ hr hd
    intro e
    unfold share at h
    rw [Finset.prod_eq_zero hi e, zero_mul] at h
    exact h rfl
  intro hi
  apply q.chosen_lt _ _ hd
  intro e
  unfold share at h
  rw [Finset.prod_eq_zero (Finset.mem_compl.mpr hi) e, mul_zero] at h
  exact h rfl

end table

def fineShare (S : StepData c f) (x : ℝ) (U : Config G f) (s : Finset (Cell f)) :=
  q.share s (toll U) (fiery G x S.patch.L / 4)

def bondShare (S : StepData c f) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c)
    (s : Finset (Bond c)) := q.share s (wire (S.prediction U k) V) (W*fiery G x S.patch.L)

/-- Keep precisely the actual `D'`, no extra mass per site. -/
def distribute (A : Stores S) (x W : ℝ) (U : Config G f) (k : S.Choices) (V : Config G c) :=
  if RG.flags (temp x) V = A.flags then
    q.fineShare S x U A.costs * q.bondShare S x W U k V A.aisles else 0

/-- E's profile partition. Positivity of the two scales here matters;
at zero temperature/width the quotient formulas for χ don't have these
guards (use `hard` if needed). -/
def profiles (G : Gauge) (S : StepData c f) (x W : ℝ) (h : 0 < W) (he : 0 < fiery G x S.patch.L) :
    Allocation G S x W where
  bill A k U V := q.distribute A x W U k V
  nonneg := by intros; unfold distribute; split
               · exact mul_nonneg (q.share_nonneg ..) (q.share_nonneg ..)
               rfl
  sums := by
    intro k U V
    rw [← Equiv.sum_comp (inventory S).symm]
    rw [Fintype.sum_prod_type]; simp_rw [Fintype.sum_prod_type]
    unfold distribute
    simp only [inventory, Equiv.coe_fn_symm_mk, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      fineShare, bondShare, ← Finset.mul_sum, q.share_sum, mul_one]
  borel := by
    intro hb A k
    unfold distribute fineShare bondShare
    have hf : MeasurableSet {a : Config G f × Config G c | RG.flags (temp x) a.2 = A.flags} :=
      measurable_snd (RG.flags_measurable_eq _ _)
    apply Measurable.ite hf _ measurable_const
    apply Measurable.mul
    · exact q.share_meas _ (fun a : Config G f × Config G c => toll a.1)
        (fun i => toll_meas i measurable_fst) _
    exact q.share_meas _ (fun a : Config G f × Config G c => wire (S.prediction a.1 k) a.2)
      (fun i => wire_meas k i hb measurable_fst measurable_snd) _
  actual := by
    intro A k U V hv
    unfold distribute at hv; split at hv
    · rename_i he'
      have hu := left_ne_zero_of_mul hv
      have hm := right_ne_zero_of_mul hv
      refine ⟨fun i => ?_, fun i => ?_, he'.symm⟩
      · obtain ⟨hl,hr⟩ := q.share_cuts _ _ _ hu (by positivity) i (G.chord_nonneg _)
        exact ⟨fun hi => (hl hi).le, fun hi => by linarith [hr hi]⟩
      obtain ⟨hl,hr⟩ := q.share_cuts _ _ _ hm (by positivity) i (G.chord_nonneg _)
      refine ⟨fun hi => (hl hi).le, fun hi => ?_⟩
      rw [mul_assoc]; exact (hr hi).le
    exact (hv rfl).elim

end Chi
end YM.Push.SectorMeasure
