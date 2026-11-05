import YM.Extra.MULTISOURCE_BOUNDS.Forks



/-!
# Bounded products of held operands at the actual addresses of the input

Vacuum letters costed separately, including reset. No locality claim about
products of expectation values. Retain masks and counted histories.
Unwrapping never used here. Include tie to flags/sectors before producing
local alphabets. In particular budget measures on these products are not
assuming variations of H across a mask boundary even at zeroth order.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter MeasureTheory Lattice RG Wilson Precision Labels Marker Overlay Extra.Multi Extra.Multi.Merger Tree
 
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {n m : Side} {V : Type} [DecidableEq V] {R : Census V} {P : Rep G n}
    (L : Bands R P) {α β : Type}

/-- Actual old fine operand, including final mask if regular. Gas
occurrence retains all the flags and tests of P; never invert a K. -/
def old : Pieces→Config G n → ℂ := Sum.elim
    (fun i => masked P.p.threshold (L.support i) (L.H i)) fun i => L.entries i.1 i.2

lemma home (h : L.Active) (i : Pieces) : LocalOn (inspected (blocks L i)) (old L i) := by
  cases i with
  | inr i => exact UsesFinal.allReads _ _ _ (h.inspects i.1 i.2)
  | inl i =>
    intro x y H; have he : Healthy P.p.threshold (L.support i) x ↔ Healthy P.p.threshold (L.support i) y := by
      unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty, flags_agree _ _ _ (L.support i) H]
    by_cases ht : Healthy P.p.threshold (L.support i) x
    · simp only [old,Sum.elim_inl, masked_eq _ _ _ _ ht,masked_eq _ _ _ _ (he.mp ht)]
      exact (h.regular i).sites _ _ (agrees_mono H fun _ hz => Finset.mem_union_left _ hz)
    simp only [old,Sum.elim_inl,masked_ne _ _ _ _ ht,masked_ne _ _ _ _ (mt he.mpr ht)]

lemma old_meas (h : L.Active) (i : Pieces) : Measurable (old L i) :=
  Sum.rec (motive:=fun i => Measurable (old L i)) (fun i => masked_measurable _ _ _ (h.regular i).borel)
    (fun i => h.meas i.1 i.2) i


lemma old_bounded {κ : ℝ} (h : L.Active) {e : Pieces→ℝ} (he : Inbox L κ e) (hp : κ ≤ 1) (i : Pieces) (y) : ‖old L i y‖ ≤ e i := by
  cases i with
  | inl i =>
    obtain ⟨v,hv⟩ := h.proper i
    by_cases h : Healthy P.p.threshold (L.support i) y
    · rw [show old L (.inl i) y=_ from masked_eq _ _ _ _ h]
      exact (he.regular i v hv).2 y h [] (by simp) (by simp)
    rw [show old L (.inl i) y=0 from masked_ne _ _ _ _ h,norm_zero]; exact he.pos _
  | inr i => exact (he.gas i.1 i.2 y).trans (mul_le_of_le_one_left (he.pos _) hp)

abbrev wave (f : α → Pieces) : α ⊕ β → Config G n → ℂ := Sum.elim (fun i => old L (f i)) fun _ _ => 1
abbrev metric (f : α → Pieces) (e : Pieces→ℝ) : α⊕β→ℝ := Sum.elim (e ∘ f) (fun _ => 1)

abbrev Chain (α : Type) := Extra.Multi.Repeated.Tuple α

variable (x : Chain (α⊕β)) (F : α → Pieces)

-- Tuple version: nonempty (connected component after pricing). Can have
-- repeated addresses. Old factors not on vacuum ids; those evaluated later.
def ink (U : Config G n) : ℂ := ∏ i,wave L F (x.2 i) U
lemma ink_meas (h : L.Active) : Measurable (ink L x F) := by
  apply Finset.measurable_fun_prod; intro i _
  cases x.2 i
  case inl a => exact old_meas L h _
  case inr b => exact measurable_const

lemma ink_bound (h : L.Active) {κ : ℝ} {e : Pieces→ℝ} (he : Inbox L κ e) (hp : κ ≤ 1) (U : Config G n) :
    ‖ink L x F U‖ ≤ ∏ i, metric F e (x.2 i) := by
  unfold ink; rw [norm_prod]; exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => by
    cases x.2 i
    case inl j => exact old_bounded L h he hp _ _
    case inr j => dsimp only [wave,Sum.elim_inr,metric]; exact norm_one.le


end YM.Further.DenseMixedKernels
