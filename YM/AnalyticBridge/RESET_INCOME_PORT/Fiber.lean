import YM.AnalyticBridge.RESET_INCOME_PORT.Journal
import YM.AnalyticBridge.RESET_INCOME_PORT.Slips
import YM.Next.SCHEDULE.Resize


set_option warningAsError false

/-!
# Log-route Income.Meter

Gives the exact `varies` predicate from moving gas estimates from paired
leg integrals. Conditional on specified trials, probes & true recipes at
the same dials. Reprices any allocated raw-log pressure pieces contributing
to the trial F (the pressure itself may reorganize differently at the
second dial), includes authentic per-anchor cost. Covers duplication only
under an explicit joint destination pricing budget. Designed for
`Template.add` tests, hence all at unflagged V. Nothing about pricing such
moves on arclength-unbounded parameter variation or mismatched flags, no
volume-exponential exception even for movement estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.ResetIncome
open Function Filter Set Finset Lattice Wilson RG Precision Exterior Tree MeasureTheory
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure
open Next.Fluctuations.Sector Push.SectorMeasure.Oriented Push.SectorMeasure.Presented
open Next.SectorChange UVNext.CouplingReset Input RG.Supply RG.Shoot Pressure.Testing
open SectorNext.Vacuum.ReLog LogMotion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {R : Rep G f} {V : Config G c} {κ u δ : ℝ}

/-- One pricing model for trial F at all-good probes. Keep common
support/anchor for the cohort, assign the full numerical logs including
all components in that Price. Further correction costs still need paying.
Can omit an address by factor zero (including if its origin is ∅).
Extra motion, e.g. subtracting a varying forecast or projection correction,
priced *per anchor* under the Trial currency. -/
structure Route (c : Side) where
  origin : ℕ → Support c
  cover : ℕ → RegularAddress c
  factor : ℕ → ℝ
  extendsReads i : origin i ⊆ (cover i).support
  kept i : factor i ≠ 0 → (cover i).site ∈ origin i
  clamp : ℝ → ℕ → ℝ -- other localized prices (x,V fixed in comparisons here)
  scale : ℝ
  other : ℕ → ℝ
  pool : ℝ
  hire : ℝ

namespace Route
variable (w : Route c)

structure Carries (x b a : ℝ) (T : Template G c) (R : Rep G f) (V : Config G c) (d d' : HeadGas e)
    (v : HeadGas.View e) (κ : ℝ) : Prop where
  scale : 0≤w.scale
  built : HeadGas.Supported d d' v R V (w.scale*|b-a|)
  funds o : SumBudget (fun i => if (w.cover i).site=o then w.other i else 0) w.pool
  multiple (P : Support c) (o : Site c) : SumBudget (fun i =>
    if w.origin i=P ∧ (w.cover i).site=o then |w.factor i| else 0) w.hire
  spare i : 0 ≤ w.other i ∧ |w.clamp b i-w.clamp a i| ≤ w.other i * |b-a|
  room : 0≤w.hire ∧ w.scale*(w.hire*v.meter.quota)+w.pool ≤ κ
  issueL i : (T.terms x b).reg i = w.cover i ∧ (T.terms x b).E i V = w.factor i * raw d.reads d.atoms (w.origin i) V + w.clamp b i
  issueR i : (T.terms x a).reg i = w.cover i ∧ (T.terms x a).E i V = w.factor i * raw d'.reads d'.atoms (w.origin i) V + w.clamp a i

lemma Tracks {x a b κ : ℝ} {T : Template G c} {d d' : HeadGas e} {v : HeadGas.View e} (hw : w.Carries x b a T R V d d' v κ) :
    T.varies V κ x a b := by
  have hy := hw.scale; obtain ⟨hr,hl⟩ := hw.room
  obtain ⟨hx,he,hE⟩ := HeadGas.inspected hw.built (mul_nonneg hw.scale (abs_nonneg _))
  let C := locker (fumes d.reads (-v.meter.wages)); let m := native (n:=c) e.point.B v.meter.width
  let p i := w.scale*(|w.factor i| * C (w.origin i)) + w.other i
  have hz i : 0 ≤ C i := (hx i).1
  have hp i : 0 ≤ p i := add_nonneg (mul_nonneg hw.scale (mul_nonneg (abs_nonneg _) (hz _))) (hw.spare i).1
  refine ⟨p,fun i => ⟨hp i,?_⟩,fun o => ?_⟩
  · rw [(hw.issueL i).2,(hw.issueR i).2,add_sub_add_comm, ← mul_sub]
    apply (abs_add_le ..).trans; rw [abs_mul]; apply (add_le_add
      (mul_le_mul_of_nonneg_left (hx _).2 (abs_nonneg (w.factor i))) (hw.spare i).2).trans_eq
    unfold p C; ring
  simp_rw [(hw.issueR _).1]
  let q i := if (w.cover i).site=o then w.other i else 0
  let t (P : Support c) i := if w.origin i=P ∧ (w.cover i).site=o then |w.factor i| else 0
  let f (i : ℕ) := if (w.cover i).site=o then p i else 0
  have hQ : SumBudget q w.pool := hw.funds o
  let J : Finset (Support c) := Finset.univ.filter (fun i : Support c=>o∈i)
  have hj i : ∑ j∈J,t j i * C j = if (w.cover i).site=o then |w.factor i| *C (w.origin i) else 0 := by
    unfold t J
    by_cases hh : w.factor i = 0
    · simp [hh]
    by_cases he : (w.cover i).site = o
    · have ha : o∈w.origin i := he ▸ w.kept i hh
      simp [he,ite_mul,ha]
    simp [he]
  have hf : f = fun i => w.scale*(∑ j∈J,t j i*C j)+q i := by
    funext i; rw [hj]; unfold f q; split <;> simp [*,p]
  have hT j := (hw.multiple j o).2.1.mul_right (C j)
  have H : Summable f := by rw [hf]; exact ((summable_sum fun i _ => hT i).mul_left _).add hQ.2.1
  refine ⟨fun i => (by change 0 ≤ f i; unfold f; split; exact hp i; rfl),H,?_⟩
  change ∑' i, f i ≤ _
  rw [hf, Summable.tsum_add ((summable_sum fun i _=> hT i).mul_left _) hQ.2.1,tsum_mul_left,
    Summable.tsum_finsetSum fun i _ => hT i]
  have hg (i : Support c) : 1 ≤ m i := (native_rate _ hw.built.affix.nonnegative).pos i
  have hPiece (P : Support c) : ∑' i, t P i*C P ≤ w.hire*(m P * C P) := by
    rw [tsum_mul_right]; exact (mul_le_mul_of_nonneg_right (hw.multiple _ _).2.2 (hz _)).trans
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (hz P) (hg _)) hr)
  have h' : ∑ i∈J,m i*C i ≤ v.meter.quota := he.hits o
  apply le_trans _ hl; refine add_le_add (mul_le_mul_of_nonneg_left ?_ hy) hQ.2.2
  exact (sum_le_sum fun i _ => hPiece i).trans (by rw [←Finset.mul_sum]; exact mul_le_mul_of_nonneg_left h' hr)
end Route

section live
variable {b : Sheet G} {D : Rolls b} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Directed G I Z K P)
    {s : Set ℝ} {q : ResetPrices} {N m p : ℕ} {F : Terms B.a m p}


end live
end YM.AnalyticBridge.ResetIncome
