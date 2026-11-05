import YM.Marker.Weight
/-! Actual Taylor exponential used on probabilities. -/
set_option autoImplicit false
noncomputable section
namespace YM.Marker.Poly
open Function Finset Filter Set MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {V : Type*} [DecidableEq V] {R : Census V}

lemma high (a : Poly R) (ha : a.part R.quiet=0) (k : ℕ) (b : R.Mode) (hb : b.val.card<k) : (a^k).part b=0 := by
  induction k generalizing b with
  | zero => omega
  | succ k h =>
    rw [pow_succ,part_mul]
    refine sum_eq_zero fun x _ => sum_eq_zero fun y _ => ?_
    split <;> rename_i he
    · by_cases e : y=R.quiet
      · simp only [e,ha,mul_zero]
      have hh : 0 < y.val.card := card_pos.mpr (nonempty_iff_ne_empty.mpr fun H => e (Subtype.ext H))
      have hx : b.val.card=x.val.card+y.val.card := by rw [← he.2, card_union_of_disjoint he.1]
      rw [h _ (by omega),zero_mul]
    rfl

section
variable [Fintype V]
lemma stops (a : Poly R) (ha : a.part R.quiet=0) (k : ℕ) (he : Fintype.card V < k) : a^k=0 := by
  ext i; rw [part_nil, high a ha k i (lt_of_le_of_lt (card_le_univ _) he)]

def pass (a : Poly R) : Poly R := ∑ i∈Finset.range (Fintype.card V+1),(i.factorial:ℂ)⁻¹ • a^i

lemma pass_part (a : Poly R) (ha : a.part R.quiet=0) : (pass a).part R.quiet=1 := by
  unfold pass; rw [part_sum, sum_eq_single 0]
  · simp
  · intro b _ h; rw [part_smul, high a ha b R.quiet ?_,mul_zero]; simpa [Census.quiet] using Nat.pos_of_ne_zero h
  simp

@[fun_prop] lemma pass_cont : Continuous (pass (V:=V) (R:=R)) := by unfold pass; fun_prop

lemma pass_budget {w : V → ℝ} (hw : ∀ i,0<w i) (a : Poly R) : price w (pass a)≤Real.exp (price w a) := by
  apply le_trans (batch hw _ _)
  have HH : HasSum (fun i : ℕ => price w a^i / i.factorial) (Real.exp (price w a)) := by
    convert! NormedSpace.expSeries_div_hasSum_exp (price w a) using 1
    rw [Real.exp_eq_exp_ℝ]
  refine le_trans (b:=∑ i∈Finset.range (Fintype.card V+1),price w a^i / i.factorial) (sum_le_sum ?_) ?_
  · intro i _; rw [adapted]; apply le_trans (mul_le_mul_of_nonneg_left (powers hw _ _) (norm_nonneg _)); simp [div_eq_mul_inv,mul_comm]
  rw [← HH.tsum_eq]; exact HH.summable.sum_le_tsum _ (fun i _ => by have := nonnegative hw a; positivity)
end

/-- Need for integration of output family. Requires actual convergence with
respect to these **same** weights. -/
lemma budgeted {M} {f : M → Poly R} {b : M → ℝ} {w : V → ℝ} (hw : ∀ x,0 < w x)
    (hb : Summable b) (H : ∀ i, price w (f i) ≤ b i) : Summable f ∧ price w (∑' i,f i) ≤ ∑' i,b i := by
  have hs : Summable f := by
    obtain ⟨k,h,h'⟩ := equivalent_norm (R:=R) hw
    exact ((hb.mul_right k).of_nonneg_of_le (fun i => norm_nonneg _) (fun i => (h' (f i)).trans <|
      mul_le_mul_of_nonneg_right (H i) h)).of_norm
  refine ⟨hs,le_of_tendsto_of_tendsto ((price_cont w).continuousAt.tendsto.comp hs.hasSum) hb.hasSum ?_⟩
  exact Eventually.of_forall fun i => (batch hw i f).trans (sum_le_sum fun j _ ↦ H j)

lemma share {M} {f : M → Poly R} (hs : Summable f) (i : R.Mode) : part (∑' m,f m) i=∑' m,(f m).part i := (get i).map_tsum hs

instance : MeasurableSpace (Poly R) := borel _
instance : BorelSpace (Poly R) := ⟨rfl⟩
instance : SecondCountableTopology (Poly R) := inferInstanceAs (SecondCountableTopology (R.Mode → ℂ))
end YM.Marker.Poly
