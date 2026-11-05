import YM.Extra.SOURCE_HISTORIES.Till

/-! Product of a bad-stencil multiplier with the EXACT forced expression
at birth, incl all predicates. Address and budget receipts. -/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {n : Side} {G : Gauge} {d : ℕ}

/-- One forced slot in E's/bid's literal address space. K may be nonzero on
that slot too. -/
structure SlotFit (R : Rep G n) (o : Site n) (i : ℕ) (f : Config G n → ℂ) : Prop where
  invariant : GaugeInvariant f
  borel : Measurable f
  read : UsesFinal R.p.threshold (R.activities.forced i).support f
  tagged : f ≠ 0 → o ∈ (R.activities.forced i).support
  permits U : f U ≠ 0 → (R.activities.forced i).eligible R.p.threshold U

lemma slot_zero (R : Rep G n) (o i) : SlotFit R o i 0 :=
  ⟨fun _ _ => rfl, measurable_const,fun _ _ _ _ => rfl, fun x => (x rfl).elim,fun _ x => (x rfl).elim⟩

namespace Attach
variable (R : Rep G n) (Y : Support n) (H : Shelf R.activities) (q : ℕ)

open scoped Classical in
/-- Unmarked entries not affected. Enforce exact inventory and all old
K factors (hence their tests). K predicates on extra p val data matter
on each input. -/
def chunk (b : Cluster R Y) (f : Config G n → ℂ) (U : Config G n) : ℂ :=
  if span R Y b ∩ flags R.p.threshold U = debts R Y b then
    f U * ∏ i ∈ b.val, (R.activities.K i U : ℂ)
  else 0

lemma narrow (S T : Support n) (ht : S ⊆ T) (A B : Support n) (h : T∩A=T∩B) : S∩A=S∩B := by
  ext x
  simp only [Finset.mem_inter]
  constructor <;> intro ⟨hx, hy⟩
  · have he : x∈T∩B := h ▸ Finset.mem_inter.mpr ⟨ht hx,hy⟩
    exact ⟨hx,(Finset.mem_inter.mp he).2⟩
  have he : x∈T∩A := h.symm ▸ Finset.mem_inter.mpr ⟨ht hx,hy⟩
  exact ⟨hx,(Finset.mem_inter.mp he).2⟩

private lemma chunk_fit {o : Site n} (ho : o∈Y) {f : Config G n → ℂ} (hs : GaugeInvariant f)
    (hf : Measurable f) (he : UsesFinal R.p.threshold Y f)
    (b : Cluster R Y) (hv : R.activities.ForcedFamily R.p) :
    SlotFit R o (stamp R Y H q b) (chunk R Y b f) := by
  classical
  let T := span R Y b
  let I := debts R Y b
  refine ⟨?_,?_,?_,fun _ => show o∈X R (stamp R Y H q b) from (stamp_x R Y H q b).symm ▸ base R Y b ho,?_⟩
  · intro k U
    simp only [chunk,gauge_flags,hs k U,hv.sym _ k U]
  · have he : MeasurableSet {U : Config G n | T ∩ flags R.p.threshold U = I} := by
      rw [show {U : Config G n | T ∩ flags R.p.threshold U = I} = ⋃ X : {X : Support n // T∩X=I},
        {U | flags R.p.threshold U = X.val} by
        ext U; simp only [mem_setOf_eq,mem_iUnion]
        exact ⟨fun h => ⟨⟨_,h⟩,rfl⟩,fun ⟨X,hX⟩ => hX.symm ▸ X.property⟩]
      exact MeasurableSet.iUnion fun i => flags_measurable_eq ..
    unfold chunk
    exact Measurable.ite he (hf.mul (Finset.measurable_fun_prod _ (fun i _ =>
      Complex.continuous_ofReal.measurable.comp (hv.meas i)))) measurable_const
  · change UsesFinal _ (X R (stamp R Y H q b)) _; rw [stamp_x]
    intro U V hA hX
    have hz : f U = f V := he _ _ (agrees_mono hA (Finset.coe_subset.mpr (base ..))) (narrow Y T (base ..) _ _ hX)
    have hw (i) (hi : i∈b.val) : R.activities.K i U = R.activities.K i V := by
      refine hv.reads i _ _ (agrees_mono hA (Finset.coe_subset.mpr (owns R Y b i hi))) ?_
      exact narrow _ T (owns R Y b i hi) _ _ hX
    have hu : ∏ i ∈ b.val,(R.activities.K i U:ℂ) = ∏ i ∈ b.val,(R.activities.K i V:ℂ) := Finset.prod_congr rfl fun i hi => by rw [hw i hi]
    unfold chunk
    simp only [hX,hz,hu]
  · intro U hu
    refine ⟨?_,H.check _ U⟩
    unfold chunk at hu
    split at hu <;> rename_i hz
    · change X R (stamp R Y H q b) ∩ _ = Attach.I R (stamp R Y H q b); rw [stamp_x,stamp_i]; exact hz
    exact (hu rfl).elim

/-- Fill the reserved cells, use zero for all others. -/
def line (f : Config G n → ℂ) : ℕ → Config G n → ℂ := extend (stamp R Y H q) (fun i => chunk R Y i f) (fun _ => 0)

lemma line_stamp (f : Config G n → ℂ) (b : Cluster R Y) :
    line R Y H q f (stamp R Y H q b) = chunk R Y b f := (stamp R Y H q).injective.extend_apply ..
lemma line_empty (f : Config G n → ℂ) {i} (hi : i∉range (stamp R Y H q)) :
    line R Y H q f i=0 := extend_apply' _ _ _ hi

theorem line_fit {o : Site n} (ho : o∈Y) {f : Config G n → ℂ} (hs : GaugeInvariant f)
    (hf : Measurable f) (he : UsesFinal R.p.threshold Y f)
    (hv : R.activities.ForcedFamily R.p) (j : ℕ) :
    SlotFit R o j (line R Y H q f j) := by
  by_cases hj : j∈range (stamp R Y H q)
  · obtain ⟨c,rfl⟩ := hj
    rw [line_stamp]
    exact chunk_fit R Y H q ho hs hf he c hv
  rw [line_empty R Y H q f hj]; exact slot_zero ..

theorem line_linear : IsLinearMap ℂ (line R Y H q) := by
  classical
  constructor
  · intro x y
    funext i U
    by_cases hj : i∈range (stamp R Y H q)
    · obtain ⟨c,rfl⟩ := hj
      simp only [line_stamp,Pi.add_apply,chunk]
      split <;> simp [add_mul]
    simp [line_empty _ _ _ _ _ hj]
  intro c y
  funext i U
  by_cases hj : i∈range (stamp R Y H q)
  · obtain ⟨b,rfl⟩ := hj
    simp only [line_stamp,Pi.smul_apply,smul_eq_mul,chunk]
    split <;> simp [mul_assoc]
  simp [line_empty _ _ _ _ _ hj]

/-- Full weighted price and explicit coefficient majorants. Works with the
actual grown A, needs only KBound at that A, even when many old labels meet
Y. -/
theorem line_budget {w : ℝ} {f : Config G n → ℂ} {C : ℝ} (hb : ∀ U, ‖f U‖ ≤ C)
    (hv : R.activities.KBound R.p w) :
    ∃ p : ℕ → ℝ, SumBudget (fun i => R.p.mass (X R i) (p i))
         (C * (R.p.mass Y 1 * (Real.exp (Y.card*w)-1))) ∧
      ∀ i, 0 ≤ p i ∧ ∀ U, ‖line R Y H q f i U‖ ≤ p i := by
  classical
  obtain ⟨a,ha,hw⟩ := hv
  let s := stamp R Y H q
  let g (c : Cluster R Y) := C * ∏ i ∈ c.val,a i
  let p : ℕ → ℝ := extend s g (fun _ => 0)
  have hc : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  have he (c) : p (s c) = g c := s.injective.extend_apply ..
  have hz (i : ℕ) (hi : i∉range s) : p i = 0 := extend_apply' _ _ _ hi
  have hh (i) : 0 ≤ p i ∧ ∀ U, ‖line R Y H q f i U‖ ≤ p i := by
    by_cases ht : i ∈ range s
    · obtain ⟨c,rfl⟩ := ht
      have hy : 0 ≤ g c := mul_nonneg hc (Finset.prod_nonneg fun j _ => (ha j).1)
      refine ⟨(he c).symm ▸ hy,fun U => ?_⟩
      rw [he,show line R Y H q f (s c) = _ from line_stamp ..]
      unfold chunk
      split
      · rw [norm_mul,norm_prod]
        exact mul_le_mul (hb U) (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ =>
          (Complex.norm_real _).trans_le ((ha i).2 U)) (Finset.prod_nonneg fun _ _ => norm_nonneg _) hc
      rw [norm_zero]; exact hy
    simp [hz _ ht, line_empty _ _ _ _ _ ht]
  refine ⟨p,?_,hh⟩
  let k := fun i => R.p.mass (X R i) (p i)
  have ht : SumBudget (k ∘ s) (C * (R.p.mass Y 1 * (Real.exp (Y.card*w)-1))) := by
    have ht := budget_scale (budget_cluster R Y (fun i => (ha i).1) hw) hc
    have hx (c : Cluster R Y) : (k ∘ s) c = C * R.p.mass (span R Y c) (∏ i∈c.val, a i) := by
      unfold comp k
      rw [he,show X R (s c)=_ from stamp_x ..]; exact mass_scale ..
    exact (funext hx).symm ▸ ht
  have hj i (hi : i∉range s) : k i=0 := by simp [k,BudgetPoint.mass,hz i hi]
  refine ⟨fun i => mul_nonneg (Real.exp_pos _).le (hh i).1,(s.injective.summable_iff hj).mp ht.2.1,?_⟩
  have hg : Function.support k ⊆ range s := by
    intro i hi
    by_contra he
    exact hi (hj _ he)
  exact (s.injective.tsum_eq hg).symm.trans_le ht.2.2

end Attach
end YM.Extra.Histories
