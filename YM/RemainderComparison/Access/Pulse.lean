import YM.RemainderComparison.Access.Trace

/-!
 # Accounting lemmas for reexpanding moments. Passive directions with
 operator prices are part of the estimate; keep the same order going up
 `trace.trunc` so that final mixed Taylor holds. Grades natural, fine
 coupling grading g, not sqrt(g).
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Trace
open Metric Set Function Filter MeasureTheory Finset
open ConnectedActivityE6 Blaze Brush PhysicalNext.Repeat
open scoped Topology ContDiff BigOperators Classical Interval ENNReal
variable {E F Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {x : E} {b d t A C v p : ℝ} {m j k : ℕ}
lemma rightLift {x : ℝ×E} {f : E→F} (h : Brush j C 1 f x.2) : Brush j C 1 (fun y:ℝ×E=> f y.2) x:= by
  have ht:= Brush.reading (ContinuousLinearMap.snd ℝ ℝ E) h (ContinuousLinearMap.norm_snd_le ..)
  rw [one_mul] at ht; exact ht
lemma paint {f : E → ℝ} {g : E→F} (hp : Brush j A 1 f x) (he : Brush j C 1 g x) :
    Brush j (A*C*3^j) 1 (fun y=> f y • g y) x := by
  have hh := ((hp.twins he (ContinuousLinearMap.lsmul ℝ ℝ)).climb (mul_le_of_le_one_left (mul_nonneg hp.nonneg he.nonneg) ContinuousLinearMap.opNorm_lsmul_le) le_rfl).trim
  rw [show (1:ℝ)+(1+1)=3 by norm_num] at hh; exact hh
lemma left_age {q : ℝ × E} (hp : ‖q.1‖ ≤ 1) : Brush j 1 1 (ContinuousLinearMap.fst ℝ ℝ E) q :=
  Brush.linearB _ hp (by rw [mul_one]; exact ContinuousLinearMap.norm_fst_le ..) zero_le_one
lemma axisPower {q : ℝ × E} (hp : ‖q.1‖ ≤ 1) : Brush j ((3^j)^m) 1 (fun y:ℝ×E => y.1^m) q := by
  induction m with
  | zero => simp only [pow_zero]; simpa only [norm_one] using! Brush.certified zero_le_one (x:=q) (k:=j) (1:ℝ)
  | succ i ih =>
    simp_rw [pow_succ]; rw [← mul_one ((3^j)^i)]
    exact paint ih (left_age (E:=E) hp)
lemma powerC {f:E→F} (hp : ‖b‖ ≤ 1) (h : Brush j A 1 f x) (i : ℕ) :
    Brush j A 1 (fun y=> b^i • f y) x:= (h.smul _).climb (mul_le_of_le_one_left h.nonneg (show ‖b^i‖ ≤ 1 from norm_pow .. |>.trans_le (pow_le_one₀ (norm_nonneg _) hp))) le_rfl

def tariff (m j : ℕ) (A : ℝ) := (((m+1:ℕ):ℝ)*(3^j)^m*A)*3^j
lemma currency (a : ℕ→E→F) {m j : ℕ} {w:ℝ×E} (hc : ‖w.1‖ ≤ 1) (h : ∀ i ≤ m, Brush j A 1 (a i) w.2) :
    Brush j (tariff m j A) 1 (polyeval m a) w := by
  unfold polyeval
  have hp : Brush j (∑ _i∈range (m+1), (3^j)^m*A*3^j) 1 (fun v : ℝ×E=> ∑ i∈range (m+1), v.1^i • a i v.2) w := Brush.spree _ _ _ zero_le_one fun i hi=> by
    rw [Finset.mem_range] at hi; replace hi : i ≤ m := by omega
    apply paint (Brush.climb (axisPower (m:=i) hc) _ le_rfl) (rightLift (x:=w) (h _ hi))
    exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) hi
  refine hp.climb ?_ le_rfl
  unfold tariff; simp only [sum_const,card_range,nsmul_eq_mul]; apply le_of_eq; ring

lemma fareval {a u : ℕ→E→F} (hp : ‖b‖ ≤ 1)
    (he : ∀ i ≤ m, Brush j A 1 (fun y=> a i y-u i y) x) :
    Brush j (((m+1:ℕ):ℝ)*A) 1 (fun y=> polyeval m a (b,y)-polyeval m u (b,y)) x := by
  unfold polyeval; simp_rw [← sum_sub_distrib,← smul_sub]
  convert Brush.spree (k:=j) (range (m+1)) (fun i y=> b^i • (a i y - u i y)) (fun _=>A) zero_le_one (fun i hi=> powerC hp (he i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) i) using 1
  simp
omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
lemma locomotion {a : ℕ → E→F} {w : ℝ} (ha : ∀ i ≤ m, ‖a i x‖ ≤ A) (hw : ‖w‖ ≤ 1) :
    ‖polyeval m a (w,x)-a 0 x‖ ≤ (m:ℝ)*A*‖w‖ := by
  unfold polyeval
  rw [Finset.sum_range_succ',pow_zero,one_smul,add_sub_cancel_right]
  have hh i (hi:i∈range m) : ‖w^(i+1) • a (i+1) x‖ ≤ A * ‖w‖ := by
    rw [norm_smul,norm_pow,mul_comm A]
    exact mul_le_mul ((pow_le_pow_of_le_one (norm_nonneg _) hw (show 1 ≤ i + 1 from Nat.le_add_left ..)).trans_eq (pow_one _)) (ha _ (Finset.mem_range.mp hi)) (norm_nonneg _) (norm_nonneg _)
  apply (norm_sum_le ..).trans ((sum_le_sum hh).trans_eq ?_)
  rw [Finset.sum_const, Finset.card_range,nsmul_eq_mul,mul_assoc]
end YM.RemainderComparison.Trace
