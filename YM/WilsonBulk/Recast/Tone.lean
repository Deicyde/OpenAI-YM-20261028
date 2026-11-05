import YM.WilsonBulk.Series.Possess

/-!
# Coefficient recursion for the coupling reset and signed power parity

Growth at each fixed order from polynomial maps of primitives used later.
Keep formal series transformation as exact constructor. General ℝ-algebra
useful for character & lipschitz. Rise solves X_f = X_c * rise ; not replace by
cont-RG analytic matter. Carries BOTH changes of variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open PowerSeries Filter Function Finset Sheet
open scoped Topology BigOperators Classical
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B]
  {p q r : PowerSeries A} {n k m : ℕ}
-- ratio, pull x→x*r. See inverse continuation elsewhere

def tempo (p : PowerSeries A) := X*p
def bar (p : PowerSeries A) : PowerSeries A →ₐ[ℝ] PowerSeries A := tuner (post A) (show constantCoeff (tempo p)=0 by simp [tempo])
lemma bar_C (p : PowerSeries A) (a : A) : bar p (C a)=C a := tuner_C ..
lemma bar_X (p : PowerSeries A) : bar p X=X*p:=tuner_X ..
lemma bar_const (p q : PowerSeries A) : constantCoeff (bar p q)=constantCoeff q := by
  unfold bar; rw [tuner_const,post_p,constantCoeff_C]
omit [Algebra ℝ A] in
lemma StepsClock (h : Steps n p q) : Steps (n+1) (X*p) (X*q):= by intro i hi; cases i; simp; rw [coeff_succ_X_mul,coeff_succ_X_mul,h _ (by omega)]
lemma barSteps {s t : PowerSeries A} (h : Steps n p q) (he : Steps (n+1) s t) : Steps (n+1) (bar p s) (bar q t) := tuneAny_agree _ (fun _=> Steps.self) (StepsClock h) he
lemma bar_at {s t : PowerSeries A} (h : Steps n p q) (he : Steps n s t) : Steps n (bar p s) (bar q t) := tuneAny_agree _ (fun _=> Steps.self) (Steps.mul (p:=X) Steps.self h) he
section
omit [Algebra ℝ A]
lemma minus_clock (h : Steps n p q) {s t : PowerSeries A} (he : Steps n s t) : Steps n (p-s) (q-t) := fun i hi=> by rw [map_sub,map_sub,h i hi,he i hi]
lemma StepsL (h : Steps n p q) (he : constantCoeff r=0) : Steps (n+1) (r*p) (r*q) := by obtain ⟨s,hs⟩:= X_dvd_iff.mpr he; rw [hs,mul_assoc,mul_assoc]; exact StepsClock (Steps.mul Steps.self h)

-- simple grade split

def Pall (p : PowerSeries A) := ∀ i,i%2≠0→ coeff i p=0
lemma Pall.square_mul {P Q : PowerSeries A} (h : Pall P) (he : Pall Q) : Pall (P*Q) := by
  intro i hi; rw [coeff_mul]; exact sum_eq_zero fun ⟨x,y⟩ hx=> by
    have he': x+y=i := mem_antidiagonal.mp hx; rcases eq_or_ne (x%2) 0 with H|H
    · rw [he y (by omega),mul_zero]
    rw [h x H,zero_mul]
lemma Pall.sq_pow {p : PowerSeries A} (h : Pall p) (n : ℕ) : Pall (p^n) := by
  induction n with
  | zero=> intro i hi; rw [pow_zero,coeff_one,if_neg (by omega)]
  | succ n ih => rw [pow_succ]; exact ih.square_mul h
-- coefficient general t. choose reorder weights
lemma priceX (i e : ℕ) (P : PowerSeries A) (he : e ≤ i) : coeff i (X^e*P)=coeff (i-e) P := by
  rw [coeff_X_pow_mul',if_pos he]
end
lemma bar_terms (p q r : PowerSeries A) (i : ℕ) : coeff i (r*bar p q)=∑ e∈range (i+1), coeff (i-e) (p^e*r)*coeff e q := by
  rw [Steps.mul Steps.self ((before_end (i+1) q).push (bar p) (by rw [bar_X]; simp)) i (by omega) (p:=r) ]; -- syntax
  simp_rw [map_sum,map_mul,map_pow,bar_X,bar_C,mul_pow,Finset.mul_sum,map_sum]; refine sum_congr rfl fun j hj=>?_ -- `map_mul` hitting coeff !
  rw [show r*(X^j*p^j*C (coeff j q))= X^j*(p^j*r*C (coeff j q)) from by ring, priceX i j _ (by rw [mem_range] at hj; omega),coeff_mul_C]

lemma Pall.bar {p q : PowerSeries A} (h : Pall p) (he : Pall q) : Pall (Recall.bar p q) := by
  intro i hi; rw [← one_mul (Recall.bar p q),bar_terms]; refine sum_eq_zero fun j hj=>?_ ; rw [mul_one]; rcases eq_or_ne (j%2) 0 with hJ|hJ
  · rw [h.sq_pow j (i-j) (by rw [mem_range] at hj; omega),zero_mul]
  rw [he j hJ,mul_zero] -- layout
end YM.WilsonBulk.Recall
