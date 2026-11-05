import YM.Next.RANK.Radian.Boilers

/-!
# Basic symbol estimate calculus on window

Uncompact tails separately. Use wave minus chirp match at zero in same
Fourier sign convention on both directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric  Lattice  Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {i n j k D : ℕ} {f g : E4→ℂ} {x y c R b' : ℝ}
-- J estimates any bounded range. F may vanish outside; never use derivatives at singularity.
structure Cast (f : E4→ℂ) (n j : ℕ) (R C : ℝ) : Prop where
  positive : 0 ≤ C
  hills : ContDiffOn ℝ (↑n) f away
  altar i : i≤n → ∀ z : E4,z∈away → ‖z‖ ≤ R → ‖iteratedFDeriv ℝ i f z‖ * ‖z‖^i ≤ C * ‖z‖^j
lemma Cast.coin (h : Cast f n j R c) (ht : c ≤ y): Cast f n j R y:= ⟨h.positive.trans ht,h.hills,fun i hi z hz hZ=> (h.altar i hi z hz hZ).trans (mul_le_mul_of_nonneg_right ht (by positivity))⟩
lemma Cast.range {T : ℝ} (h : Cast f n j R x) (ht : T ≤ R): Cast f n j T x:=⟨h.positive,h.hills,fun i hi z hz he=> h.altar i hi z hz (he.trans ht)⟩

lemma Cast.join (h : Cast f n j R c) (ht : Cast g n j R b'): Cast (f+g) n j R (c+b'):= by
  have hh (f : E4→ℂ) (h : ContDiffOn ℝ (↑n) f away) z(hz : z∈away) i(hi : i≤n) := (h.of_le (show (↑i:WithTop ℕ∞) ≤ ↑n by exact_mod_cast hi) z hz).contDiffAt (open_away.mem_nhds hz)
  refine ⟨add_nonneg h.positive ht.positive,h.hills.add ht.hills,fun i hi z hz he=>?_⟩
  rw [iteratedFDeriv_add_apply (hh f h.hills z hz i hi) (hh g ht.hills z hz i hi),add_mul]
  apply (mul_le_mul_of_nonneg_right (norm_add_le ..) (pow_nonneg (norm_nonneg _) _)).trans;rw [add_mul];exact add_le_add (h.altar i hi z hz he) (ht.altar i hi z hz he)

lemma Cast.multiply (h : Cast f n i R c) (hp : Cast g n j R b') : Cast (f*g) n (i+j) R (2^n*(c*b')):= by
  have ha:= h.positive; have hb:=hp.positive
  refine ⟨by positivity,h.hills.mul hp.hills,fun m hM z hz H=>?_⟩
  let x:= ‖z‖; let L:= c*b'*x^(i+j)
  have hu : 0 ≤ L:= by unfold L x; positivity
  have h' : 0<x:= norm_pos_iff.mpr hz
  apply (mul_le_mul_of_nonneg_right (stove away open_away (n:=m) (h.hills.of_le (by exact_mod_cast hM)) (hp.hills.of_le (by exact_mod_cast hM)) _ hz) (pow_nonneg (norm_nonneg _) _)).trans;rw [sum_mul]; apply le_trans (b:=∑ k∈Finset.range (m+1),(m.choose k:ℝ)*L)
  · refine sum_le_sum fun b hx=> ?_; have hf:b≤m:= Nat.le_of_lt_succ (mem_range.mp hx)
    have hv := mul_le_mul (h.altar b (by omega) z hz H) (hp.altar (m-b) (by omega) z hz H) (by positivity) (by positivity)
    have hx: L=(c*x^i)*(b'*x^j):=by unfold L; rw [pow_add]; ring
    rw [hx]; have he : x^m=x^b*x^(m-b):= by rw [← pow_add,Nat.add_sub_of_le hf]
    change (_*_)*x^m ≤ _; rw [he]; linarith only [mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg (α:=ℝ) (m.choose b))]
  rw [← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose]; push_cast
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : 1≤ (2:ℝ)) hM) hu).trans_eq (mul_assoc ..).symm
lemma epithet (f : E4→ℂ) (h : ContDiff ℝ ∞ f) (R : ℝ) (n : ℕ) : ∃ c,Cast f n 0 R c:= by
  choose C hC using fun i : Fin (n+1)=> (ProperSpace.isCompact_closedBall (0:E4) R).exists_bound_of_continuousOn
    (((h.continuous_iteratedFDeriv (m:=i.val) (WithTop.coe_le_coe.mpr le_top)).norm.mul (continuous_norm.pow i.val)).continuousOn)
  let J:= ∑ i, |C i|
  refine ⟨J, Finset.sum_nonneg (fun i _=> abs_nonneg _),h.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top),fun i hi z hz he=> ?_⟩
  rw [pow_zero, mul_one]
  let v:Fin (n+1):=⟨i,by omega⟩
  have hp := hC v z (show z∈ Metric.closedBall 0 R by simpa using he)
  change ‖‖iteratedFDeriv ℝ i f z‖ * ‖z‖^i‖ ≤ C v at hp
  rw [Real.norm_of_nonneg (by positivity)] at hp; exact hp.trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|C i|) (fun i _=>abs_nonneg _) (mem_univ v)))
lemma compass {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E4→F) (h : ContDiff ℝ ∞ f) : ∃ c : ℝ,0 ≤ c ∧ ∀ x : E4, ‖x‖≤1 → ‖f x-f 0‖ ≤c*‖x‖:= by
  have hF : Continuous (fderiv ℝ f):= h.continuous_fderiv (by simp)
  obtain ⟨c,H⟩:= (ProperSpace.isCompact_closedBall (0:E4) 1).exists_bound_of_continuousOn hF.continuousOn
  have ht : (0:E4)∈closedBall (0:E4) 1:=by simp
  refine ⟨c,(norm_nonneg _).trans (H 0 ht),fun x hx=>?_⟩
  simpa only [sub_zero] using (convex_closedBall (0:E4) 1).norm_image_sub_le_of_norm_fderiv_le (fun i _=>h.differentiable (by simp) i) H ht (show x∈ Metric.closedBall (0:E4) 1 by simpa using hx)
private lemma axis_bounds (f : E4→ℂ) (h : ContDiff ℝ ∞ f) (n : ℕ): ∃ C : ℝ,0≤C ∧ ∀ j≤n, ∀ x : E4, ‖x‖ ≤ 1 → ‖iteratedFDeriv ℝ j f x‖ ≤ C:= by
  choose c hc using fun i : Fin (n+1) => (ProperSpace.isCompact_closedBall (0:E4) 1).exists_bound_of_continuousOn (h.continuous_iteratedFDeriv (m:=i.val) (WithTop.coe_le_coe.mpr le_top)).continuousOn
  refine ⟨∑ i, |c i|,Finset.sum_nonneg fun _ _=> abs_nonneg _,fun j hj z hz=>?_⟩; let i:Fin (n+1):=⟨j,by omega⟩; exact (hc i z (show z∈ Metric.closedBall 0 1 by simpa using hz)).trans ((le_abs_self _).trans (single_le_sum (f:=fun i=>|c i|) (fun i _=>abs_nonneg _) (mem_univ _)))
lemma vertex {f : E4→ℂ} (h : ContDiff ℝ ∞ f) (he : f 0=0) (n : ℕ) : ∃ c, Cast f n 1 1 c:= by
  obtain ⟨c,hC,hx⟩:=compass f h; obtain ⟨b,hB,hp⟩:= axis_bounds f h n
  refine ⟨c+b, add_nonneg hC hB,h.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top),fun i hi v hz hv=>?_⟩
  cases i with
  | zero=> rw [pow_zero,mul_one,norm_iteratedFDeriv_zero,pow_one]; apply le_trans _ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (norm_nonneg _)); exact (by simpa only [he,sub_zero] using hx v hv)
  | succ i=>exact mul_le_mul ((hp _ hi v hv).trans (le_add_of_nonneg_left hC)) (pow_le_pow_of_le_one (norm_nonneg _) hv (by omega)) (by positivity) (by positivity)
lemma polarDay {f : E4→ℂ} (h : ContDiff ℝ ∞ f) (he : f 0=0) (hv : fderiv ℝ f 0=0) (n) : ∃ c,Cast f n 2 1 c:= by
  obtain ⟨c,hc,hx⟩:=compass (fderiv ℝ f) (h.fderiv_right (by simp))
  obtain ⟨b,hB,hβ⟩:= axis_bounds f h n
  have hp (x) (h : ‖x‖ ≤ 1) : ‖fderiv ℝ f x‖ ≤ c*‖x‖:= by simpa only [hv,sub_zero] using hx x h
  refine ⟨c+b,add_nonneg hc hB,h.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top),fun i hi x hz ht=>?_⟩
  by_cases H:2≤ i
  · exact mul_le_mul ((hβ _ hi x ht).trans (le_add_of_nonneg_left hc)) (pow_le_pow_of_le_one (norm_nonneg _) ht H) (by positivity) (by positivity)
  interval_cases i
  · rw [pow_zero,mul_one,norm_iteratedFDeriv_zero]
    have hb i(hi:i∈closedBall (0:E4) ‖x‖): ‖fderiv ℝ f i‖ ≤ c*‖x‖:= by
      have hv:‖i‖≤‖x‖:=by simpa using hi
      exact (hp i (hv.trans ht)).trans (mul_le_mul_of_nonneg_left hv hc)
    have hh:= (convex_closedBall (0:E4) ‖x‖).norm_image_sub_le_of_norm_fderiv_le (fun i _=>h.differentiable (by simp) i) hb (show 0∈Metric.closedBall (0:E4) ‖x‖ by simp) (show x∈Metric.closedBall 0 ‖x‖ by simp)
    simp_rw [he,sub_zero] at hh; rw [mul_assoc,← pow_two] at hh; exact hh.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (by positivity))
  rw [pow_one,norm_iteratedFDeriv_one];apply (mul_le_mul_of_nonneg_right (hp x ht) (norm_nonneg _)).trans;rw [mul_assoc,← pow_two]; exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) (by positivity)
end YM.Next.Rank.Radian
