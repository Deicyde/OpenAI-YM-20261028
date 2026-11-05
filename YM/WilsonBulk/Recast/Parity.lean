import YM.WilsonBulk.Recast.Mask

/-! # Budget mechanics: Preserves curvature-graded axis parity. Applies to EVERY step (top etc).
Needed for preserving during construction. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open Function Filter PowerSeries Finset Equiv Sheet
open scoped Topology Classical BigOperators
variable {A B X' : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] {p r q : PowerSeries A} {n : ℕ}

omit [Algebra ℝ A] in
lemma Pall.one : Pall (1:PowerSeries A) := by intro i hi; rw [coeff_one,if_neg (by omega)]
lemma Pall.scale (hf : Pall p) (c : ℝ) : Pall (c • p) := by intro i hi; rw [coeff_smul,hf _ hi,smul_zero]
omit [Algebra ℝ A] in
lemma Pall.plus (hf : Pall p) (he : Pall q) : Pall (p+q) := fun i hi=> by rw [map_add,hf _ hi,he _ hi,add_zero]
omit [Algebra ℝ A] in
lemma Pall.sub (hf : Pall p) (he : Pall q) : Pall (p-q) := fun i hi=> by rw [map_sub,hf _ hi,he _ hi,sub_self]
omit [Algebra ℝ A] in
lemma Pall.saga (F : PowerSeries A→PowerSeries A) (he : ∀ p, Pall p → Pall (F p)) : Pall (Recall.saga F) := by
  have hx (j : ℕ) : Pall (F^[j] 1) := by induction j with
    | zero=>exact Pall.one
    | succ j ih=> rw [Function.iterate_succ_apply']; exact he _ ih
  intro i hi; rw [Recall.saga,coeff_mk]; exact hx _ _ hi
lemma Pall.arises (he : Pall q) : Pall (Recall.arises q) := Pall.saga _ (fun _ hp=> Pall.one.plus (Pall.scale ((he.sub Pall.one).sub ((hp.sub Pall.one).sq_pow 2)) _))
lemma Pall.polling (he : Pall q) : Pall (Recall.polling q) := Pall.saga _ (fun _ hv=> Pall.one.plus (Pall.scale (((hv.bar he).sub Pall.one).sub ((hv.sub Pall.one).sq_pow 2)) _))
omit [Algebra ℝ A] in
lemma Pall.recovery (he : Pall p) (hq : constantCoeff p=1) : Pall (recover p) := by
  have ht := rec_one hq; let q:= recover p
  intro i hi; induction i using Nat.strong_induction_on with
  | h i ih =>
    obtain ⟨v,rfl⟩: ∃ v,i=v+1:= by cases i; simp_all; exact ⟨_,rfl⟩
    let i:=v+1
    have hh : (∑ j∈range (i+1),coeff j q*coeff (i-j) p)=0 := by rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun j k=> coeff j q*coeff k p), ← coeff_mul, ht, coeff_one]; exact if_neg (by unfold i; omega)
    rw [sum_range_succ, tsub_self, coeff_zero_eq_constantCoeff, hq,mul_one, sum_eq_zero ?_,zero_add] at hh; exact hh
    intro j hj; have hl:j < i:= mem_range.mp hj
    rcases eq_or_ne (j%2) 0 with h|h
    · rw [he (i-j) (by unfold i at *; omega),mul_zero]
    rw [show coeff j q=0 from ih j hl h, zero_mul]
lemma Pall.castback (he : Pall p) (hq : constantCoeff p=1) : Pall (yesterday p) := he.arises.recovery (arises_rule hq).1
-- through order bounds: from earlier degrees of same clock.Initialize parity or none.
lemma decision_initial (p q : PowerSeries A) (a b : PowerSeries A) (hp : Steps n a b) (hf : Steps n p q) : Steps n (1+(1/2:ℝ) • (a-1-(p-1)^2)) (1+(1/2:ℝ) • (b-1-(q-1)^2)) := Steps.add Steps.self ((minus_clock (minus_clock hp Steps.self) ((minus_clock hf Steps.self).powers 2)).scale _)
omit [Algebra ℝ A] in
lemma partner {F G : PowerSeries A→ PowerSeries A} (h : ∀ v w, Steps n v w → Steps n (F v) (G w)) (he : Poised F) (hp : Poised G) : Steps n (saga F) (saga G) := by
  have hg (i): Steps n (F^[i] 1) (G^[i] 1):= by induction i with
    | zero=> exact Steps.self
    | succ j ih=> rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact h _ _ ih
  exact (Steps.trans (he.seasons n) (Steps.trans (hg n) (hp.seasons n).symm))
lemma arisingSteps (hp : constantCoeff p=1) (hq : constantCoeff q=1) (h : Steps n p q) : Steps n (arises p) (arises q) := partner (fun x y h'=> decision_initial x y _ _ h h') (arise_safely hp) (arise_safely hq)
lemma pollingSteps (hp : constantCoeff p=1) (hq : constantCoeff q=1) (h : Steps n p q) : Steps n (polling p) (polling q) := partner (fun x y h'=> decision_initial x y _ _ (bar_at h' h) h') (poll_safe hp) (poll_safe hq)
omit [Algebra ℝ A] in
lemma recoveredSteps (hp : constantCoeff p=1) (hq : constantCoeff q=1) (h : Steps n p q) : Steps n (recover p) (recover q) := by
  suffices Steps n (recover p*(recover q*q)) (recover q*(recover p*p)) by rw [rec_one hp, rec_one hq, mul_one,mul_one] at this; exact this
  rw [mul_left_comm (recover p)]; exact Steps.mul Steps.self (Steps.mul Steps.self h.symm)
lemma pacedSteps (hp : constantCoeff p=1) (hq : constantCoeff q=1) (h : Steps n p q) : Steps n (yesterday p) (yesterday q) := recoveredSteps (arises_rule hp).1 (arises_rule hq).1 (arisingSteps hp hq h)
end YM.WilsonBulk.Recall
