import YM.MultiNext.VACUUM_STABILITY.Environs
import YM.MultiNext.VACUUM_STABILITY.Hits
import YM.MultiNext.VACUUM_STABILITY.Jets

set_option warningAsError false

/-!
# Charging unmasked payloads of ordinary complex cluster words
-/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Vacuum.Jets
open RG Lattice Wilson Filter Finset Function MeasureTheory Text  Syllable Corona Puff
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {I : Type} {n : Side} {G : Gauge}

def rate (P : BudgetPoint) (N : ℕ) := (1+(Hits.stride P.B:ℝ))^P.power * (1+(N:ℝ))^(P.power+1)

def baseFee (P : BudgetPoint) := ((1+(Hits.stride P.B:ℝ))^P.power)^P.order *
    ((((P.power+1)*P.order).factorial:ℕ):ℝ) * Real.exp 1

lemma rate_hi (P : BudgetPoint) (N : ℕ) : 1 ≤ rate P N := one_le_mul_of_one_le_of_one_le
  (one_le_pow₀ (by simp)) (one_le_pow₀ (by simp))

lemma base_pos (P : BudgetPoint) : 0 < baseFee P := by unfold baseFee; positivity

lemma annual (P : BudgetPoint) (N : ℕ) : (rate P N)^P.order ≤ baseFee P * Real.exp N := by
  let k := (P.power+1)*P.order
  unfold rate baseFee; rw [mul_pow,←pow_mul,mul_assoc _ _ (Real.exp 1),mul_assoc,mul_assoc _ (Real.exp 1),←pow_mul,←Real.exp_add]
  -- use a single term of exp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (inv_mul_le_iff₀ (show (0:ℝ)<k.factorial by positivity)).mp (Absolute.little (Absolute.rexp (1+(N:ℝ)) (by positivity)) k)

lemma rate_price (P : BudgetPoint) (N i : ℕ) (hi : i ≤ N) :
    (i:ℝ)*(1+(N*Hits.stride P.B:ℕ))^P.power ≤ rate P N := by
  unfold rate; push_cast; rw [pow_succ,←mul_assoc,←mul_pow,mul_comm (i:ℝ)]; gcongr
  · nlinarith [Nat.cast_nonneg (α:=ℝ) N, Nat.cast_nonneg (α:=ℝ) (Hits.stride P.B)]
  exact (show (i:ℝ) ≤ N by exact_mod_cast hi).trans (by simp)

variable (X : I → Support n) (F : I → Config G n → ℂ) (P : BudgetPoint)

private def heard (l : List I) (U : Config G n) := (l.map fun i => F i U).prod

def stanza (w : Syllable I) (U : Config G n) : ℂ := w.eval fun i => F i U

private lemma field_good (l : List I) (hh : ∀ i, P.Regular (X i) (F i)) (Y : Support n) (hk : ∀ i ∈ l, X i ⊆ Y) :
    P.Regular Y (heard F l) := by
  induction l with
  | nil => exact regular_unit ..
  | cons a l ih =>
    exact regular_mul (Next.Foundations.regular_larger (hh a) (hk a (by simp)))
      (ih fun i hi => hk i (List.mem_cons_of_mem _ hi))

lemma billed (w : Syllable I) (i : I) (hi : i ∈ w.letters) : X i ⊆ w.ground X := by
  intro x hx; exact Finset.mem_biUnion.mpr ⟨i,List.mem_toFinset.mpr hi,hx⟩

lemma stanza_regular (hh : ∀ i, P.Regular (X i) (F i)) (w : Syllable I) :
    P.Regular (w.ground X) (stanza F w) := path_scaled w.amp (field_good X F P _ hh _ <| billed X w)

private lemma join_caps (l : List I) (Y : Support n) (U : Config G n) (x : Site n) (hk : x ∈ Y) (he : Healthy P.threshold Y U)
    (N : ℕ) (hx : coverNumber P.B Y ≤ N) (hh : ∀ i, P.Regular (X i) (F i)) (o : I → Site n) (ho : ∀ i, o i ∈ X i)
    (f : I → ℝ) (hf : ∀ i, P.supBounds (o i) (X i) (F i) (f i)) (hL : ∀ i ∈ l, X i ⊆ Y) :
    Band P.order (P.dirBound x) U ((l.length:ℝ)*(1+(N*Hits.stride P.B:ℕ))^P.power) (l.map f).prod (heard F l) := by
  induction l with
  | nil =>
    simp only [List.length_nil,List.map_nil,List.prod_nil,Nat.cast_zero,zero_mul]
    exact constant_unit U (P.dirBound x) P.order
  | cons a l ih =>
    have hz : X a ⊆ Y := hL a (by simp)
    have ht : Healthy P.threshold (X a) U := Disjoint.mono_left hz he
    have hA : (separation (o a) x:ℝ) ≤ (N*Hits.stride P.B:ℕ) := by
      exact_mod_cast (Hits.distance Y P.B (hz (ho a)) hk).trans (Nat.mul_le_mul_right _ hx)
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,add_mul,one_mul,List.map_cons,List.prod_cons]
    rw [add_comm ((l.length:ℝ)*_)]
    exact (crossing ht (hh a) (hf a) hA).multiply (ih fun i hi => hL i (List.mem_cons_of_mem _ hi))

def charges (f : I → ℝ) (w : Syllable I) := w.weight f * (rate P (w.bill X P.B))^P.order

lemma stanza_bound (hh : ∀ i, P.Regular (X i) (F i)) (o : I → Site n) (ho : ∀ i, o i ∈ X i)
    (f : I → ℝ) (hf : ∀ i, P.supBounds (o i) (X i) (F i) (f i)) (w : Syllable I)
    (hk : coverNumber P.B (w.ground X) ≤ w.bill X P.B) (x : Site n) (hx : x ∈ w.ground X) :
    P.supBounds x (w.ground X) (stanza F w) (charges X P f w) := by
  let K := rate P (w.bill X P.B)
  have hp := w.weight_nonneg (fun i => (hf i).1); have hs : 1 ≤ K := rate_hi ..
  refine ⟨mul_nonneg hp (pow_nonneg (zero_le_one.trans hs) P.order),fun U hu l hl hv => ?_⟩
  have hh := (join_caps X F P w.letters (w.ground X) U x hx hu (w.bill X P.B) hk hh o ho f hf (billed X w)).scale w.amp
  apply le_trans (hh.caps l hl hv)
  unfold charges; apply mul_le_mul_of_nonneg_left _ hp
  refine le_trans (pow_le_pow_left₀ hh.sane ?_ l.length) (pow_le_pow_right₀ hs hl)
  exact rate_price _ _ _ (words_paid w X P.B fun i => ⟨o i,ho i⟩)

-- Multiplication of masked germs vs the global word mask
lemma ground_cons (w : List I) (i : I) (z : ℂ) : (Syllable.mk (i::w) z).ground X = X i ∪ (Syllable.mk w z).ground X := by
  unfold Syllable.ground; rw [List.toFinset_cons, Finset.biUnion_insert]

lemma freeze (w : Syllable I) (U : Config G n) : masked P.threshold (w.ground X) (stanza F w) U =
    w.eval (fun i => masked P.threshold (X i) (F i) U) := by
  obtain ⟨l,c⟩ := w; induction l with
  | nil =>
    apply masked_eq; simp [Healthy,ground]
  | cons i l ih =>
    let w := Syllable.mk l c
    let v := Syllable.mk (i::l) c
    have hh (f : I → ℂ) : v.eval f = f i * w.eval f := mul_left_comm ..
    rw [ground_cons]
    rw [hh,← ih]
    let h : Healthy P.threshold (X i ∪ w.ground X) U ↔ Healthy P.threshold (X i) U ∧ Healthy P.threshold (w.ground X) U := by
      unfold Healthy; simp
    by_cases he : Healthy P.threshold (X i) U
    · rw [masked_eq _ _ _ _ he]; by_cases hi : Healthy P.threshold (w.ground X) U
      · rw [masked_eq _ _ _ _ hi, masked_eq _ _ _ _ (h.mpr ⟨he,hi⟩)]; exact hh _
      rw [masked_ne _ _ _ _ hi, masked_ne _ _ _ _ (fun H => hi (h.mp H).2),mul_zero]
    rw [masked_ne _ _ _ _ (fun H => he (h.mp H).1),masked_ne _ _ _ _ he,zero_mul]

lemma limit_range (R : Support n) (w : Syllable I) (u : I → ℂ) :
    w.eval (fun i => if X i⊆R then u i else 0) = if w.ground X ⊆ R then w.eval u else 0 := by
  obtain ⟨l,c⟩ := w; induction l with
  | nil => simp [Syllable.eval,ground]
  | cons i l ih =>
    have hh (f) : (Syllable.mk (i::l) c).eval f = f i*(Syllable.mk l c).eval f := mul_left_comm ..
    rw [ground_cons,hh,hh,ih]
    split <;> split <;> simp [Finset.union_subset_iff, *]
end YM.Multi.Vacuum.Jets
