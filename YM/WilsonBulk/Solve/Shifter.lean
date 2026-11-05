import YM.WilsonBulk.Cash.Keeper

/-!
# Barrier method for polynomial-log costs on unbounded intervals

Independent of actual witnesses/calendars; owns density-norm overlap only on ℓ admissions. Uses
shifted exponent polynomial to avoid estimates of convolution but no per-step rate losses.
`MarginAt` is physical lease finite horizon. λ=e^{-(a/2)log2}. Works even if post-li
small step not meeting cubic quota, uses 3≤L. `age` arbitrary base W≥1 near reporting scale k
(not period/window length). Other signs of curvature etc orthogonal.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Function Filter Finset Lattice Schedule
open scoped Topology BigOperators Classical
variable {p q : ℝ→ℝ} {X A a b x t : ℝ} {d i m k j : ℕ}
variable (S : Schedule)
abbrev Evaluator (i : ℕ) : ℝ := (S.block i).val
lemma L_one (i : ℕ) : 1 ≤ Evaluator S i := by unfold Evaluator; exact_mod_cast (show 1≤_ from le_trans (by norm_num) (S.block_large i))
lemma L_log (i : ℕ) : Real.log 2 ≤ Real.log (Evaluator S i) := Real.log_le_log (by norm_num) (by exact_mod_cast (show 2≤_ from le_trans (by norm_num) (S.block_large i)))

lemma damp_lone (h : 0≤a) (hs : i ≤ j) : damp S a i j ≤ 1 := by unfold damp; apply Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos h (sub_nonpos.mpr ((scale_strict S).monotone hs)))
lemma age_fade (i : ℕ) (t : ℝ) : age S k t (i+1) ≤ age S k t i+Evaluator S i := by
  apply le_trans (age_up S k t (i.le_add_right 1)) (add_le_add_right ?_ _); -- `i.le_add_right` check
  rw [scale_succ,add_sub_cancel_left]; exact (Real.log_le_sub_one_of_pos (by positivity : 0 < Evaluator S i)).trans (by linarith) -- Eval abbrev
lemma damp_step_cheaper (h : a ≤ 1) : damp S a (i+1) i ≤ Evaluator S i := by
  unfold damp; rw [scale_succ,add_sub_cancel_left]
  calc
    _ ≤ Real.exp (Real.log (Evaluator S i)) := Real.exp_monotone (mul_le_of_le_one_left (Real.log_nonneg (L_one S i)) h)
    _ = Evaluator S i := Real.exp_log (zero_lt_one.trans_le (L_one S i))
lemma damp_due (h : 0≤a) : damp S a i m ≤ damp S a (i+1) m := by rw [← damp_split S a i (i+1) m]; exact mul_le_of_le_one_left (damp_pos ..).le (damp_lone S h (by omega))
lemma harvest (h : a≤1) : damp S a (i+1) m ≤ damp S a i m * Evaluator S i := by
  calc _ = damp S a (i+1) i * damp S a i m := (damp_split ..).symm
       _ ≤ Evaluator S i * damp S a i m := mul_le_mul_of_nonneg_right (damp_step_cheaper S h) (damp_pos ..).le
       _ = _ := mul_comm ..
lemma triangle_wall : damp S (a+b) i j * (damp S b j k*x) = damp S b i k * (damp S a i j*x) := by
  rw [← damp_fuse]
  rw [← damp_split S b i j k]; ring

def coversAbove (p q : ℝ→ℝ) := ∀ x, 1≤x→ p x≤ q x
structure Lullaby (a : ℝ) (t b : ℝ→ℝ) : Prop where
  bill : Tariff b
  above : coversAbove t b
  replenish (S : Schedule) (k : ℕ) (X : ℝ) (i : ℕ) : 1 ≤ X→ damp S a i (i+1)*b (age S k X (i+1))+ t (age S k X i) ≤ b (age S k X i)

abbrev schism (a : ℝ) := Real.exp (-a*Real.log 2)
lemma shiftedStep (h : 1≤ X) (ha : 0<a) (i : ℕ) (d : ℕ) (hB : 0<t) (hf : d/t ≤ a) :
    damp S (a+a) i (i+1) * (age S k X (i+1)+t)^d ≤ schism a * (age S k X i+t)^d := by
  let u:=age S k X i; let v:=age S k X (i+1); let s:=Real.log (Evaluator S i); have ht : 0≤s:= Real.log_nonneg (L_one S i); have hu : 0≤u:= zero_le_one.trans (h.trans (age_ge ..)); have hv : 0≤v:= zero_le_one.trans (h.trans (age_ge ..));
  have hz : v ≤ u+s := by convert! age_up S k X (by omega : i ≤ i + 1) using 1; unfold u s; rw [scale_succ,add_sub_cancel_left]
  have hh : damp S a i (i+1)=Real.exp (-(a*s)):= by unfold damp s; rw [scale_succ]; congr 1; ring
  have e' : v+t ≤ (u+t)*Real.exp (s/t) := by
    rw [show (u+t)*_= (u+t)*(Real.exp (s/t)-1)+(u+t) by ring]; have H': s/t≤Real.exp (s/t)-1 := by linarith only [Real.add_one_le_exp (s/t)]
    have hx := mul_le_mul (show t≤u+t from le_add_of_nonneg_left hu) H' (div_nonneg ht hB.le) ((by linarith only [hB,hu]):0≤u+t); rw [mul_div_cancel₀ s hB.ne'] at hx -- which lemma order?
    linarith only [hx,hz]
  calc
    _ ≤ (damp S a i (i+1) * damp S a i (i+1))*((u+t)*Real.exp (s/t))^d := by unfold v at *; rw [damp_fuse]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (add_nonneg hv hB.le) e' d) (damp_pos ..).le
    _ = Real.exp (-(a*s)-(a*s)+d*(s/t))*(u+t)^d := by rw [hh,mul_pow,Real.exp_add,sub_eq_add_neg (-(a*s)) _,Real.exp_add, Real.exp_nat_mul]; ring
    _ ≤ _ := by
       have hy := mul_le_mul_of_nonneg_right hf ht; rw [div_mul_eq_mul_div] at hy; apply mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (pow_nonneg (add_nonneg hu hB.le) _); unfold s at hy ⊢; rw [← mul_div_assoc]; linarith only [mul_le_mul_of_nonneg_left (L_log S i) ha.le, hy] -- maybe division syntactic

lemma lullaby (p : ℝ→ℝ) (h : Tariff p) (a : ℝ) (ha : 0<a) : ∃ q,Lullaby a p q := by
  obtain ⟨d,c,hc,hp⟩:= h.2.2; let r:= a/2; have hr : 0 < r:= half_pos ha; have hs : schism r <1:= by unfold schism; exact Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos hr) (Real.log_pos (by norm_num)))
  let t : ℝ := d/r+1; have hd : 0<t:= add_pos_of_nonneg_of_pos (div_nonneg (by positivity) hr.le) one_pos
  have hf : d/t≤r:= by
    rw [div_le_iff₀ hd]; unfold t; rw [mul_add,mul_one,mul_comm r ((d:ℝ)/r), div_mul_cancel₀ _ hr.ne']; linarith only [hr]
  let c':=c/(1-schism r); let q x:=c'*(x+t)^d
  have he: 0≤c':= div_nonneg hc (by linarith); have hX: c'*(1-schism r)=c:= div_mul_cancel₀ _ (by linarith)
  have hG : Tariff q:= (Tariff.const _ he).prod ((Tariff.one.add (Tariff.const _ hd.le)).powers d)
  have e x (hx:1≤x) : p x ≤ (1-schism r)*q x:= by unfold q; rw [← mul_assoc,mul_comm _ c',hX]; apply le_trans (hp x hx); gcongr; linarith
  refine ⟨q,hG,fun x hx=>?_,fun S k X i hx=>?_⟩
  · exact (e _ hx).trans (mul_le_of_le_one_left (hG.1 _ (zero_le_one.trans hx)) (sub_le_self _ (Real.exp_pos _).le))
  have hv := shiftedStep (k:=k) S hx hr i d hd hf
  calc
    _ ≤ schism r*q (age S k X i)+(1-schism r)*q (age S k X i) := add_le_add (by unfold q; rw [mul_left_comm _ c',mul_left_comm (schism r),show a=r+r from by unfold r; ring]; exact mul_le_mul_of_nonneg_left hv he) (e _ (hx.trans (age_ge S k X i)))
    _ = _ := by ring
end YM.WilsonBulk
