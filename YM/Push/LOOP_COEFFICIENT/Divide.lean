import YM.Laurent.Art
import YM.Push.LOOP_COEFFICIENT.ReadJets

/-!
# Analytic difference after setting one coordinate to zero

Summed telescoped monomials even at the divisor, actual continuous Laurent
symbol not a finite periodic division. Only fixed-fraction width losses here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Function Filter Set Lattice Laurent Bloch Exterior Complex Metric
open scoped Topology ContDiff BigOperators
variable {η C : ℝ} {p : Momentum} {f : Momentum → ℂ}

def mask (i : Axis) (p : Momentum) := Function.update p i 0
lemma mask_apply (i : Axis) (p : Momentum) (j : Axis) : mask i p j = if j=i then 0 else p j := Function.update_apply ..
lemma mask_diff (i : Axis) : ContDiff ℂ ω (mask i) := contDiff_pi.mpr fun j => by simp only [mask_apply]; split <;> fun_prop
@[simp] lemma mask_zero (i : Axis) : mask i 0 = 0 := by ext1; simp [mask_apply]
lemma mask_ray (i : Axis) (p : Momentum) (t : ℂ) : mask i (t • p) = t • mask i p := by ext1; simp only [mask_apply, Pi.smul_apply]; split <;> simp
lemma mask_tube (i : Axis) (hp : p ∈ Tube η) : mask i p ∈ Tube η := by intro j; rw [mask_apply]; split; simpa using (abs_nonneg _).trans_lt (hp i); exact hp j
lemma mask_period (i : Axis) (p : Momentum) (z : Cover) : mask i (p+reciprocal z) = mask i p + reciprocal (Function.update z i 0) := by
  ext1 j; simp only [mask_apply,Pi.add_apply,reciprocal, Function.update_apply]; split <;> simp
lemma mask_mode (i : Axis) (v : Cover) (p : Momentum) : mode (mask i p) v = mode p (Function.update v i 0) := by
  unfold mode; congr 2; exact Finset.sum_congr rfl fun j _ => by rw [mask_apply,Function.update_apply]; split <;> simp
lemma mask_size (i : Axis) (v : Cover) {b : ℤ} (hb : b.natAbs ≤ (v i).natAbs) : size (Function.update v i b) ≤ size v := Finset.sum_le_sum fun j _ => by rw [Function.update_apply]; split <;> simp_all
lemma mode_global (v : Cover) : ContDiff ℂ ω (fun p : Momentum => mode p v) := by unfold mode; fun_prop

def stair (u : ℤ → ℂ) (n : ℤ) := if 0 ≤ n then ∑ i ∈ Finset.range n.natAbs,u (i:ℕ) else -(∑ i ∈ Finset.range n.natAbs, u (Int.negSucc i))
lemma stair_mult (u : ℤ → ℂ) {q : ℂ} (hu : ∀ b : ℤ, q * u b = u (b+1)-u b) (n : ℤ) : q * stair u n = u n - u 0 := by
  have hp (v : ℤ → ℂ) (p : ℕ) : ∑ i ∈ Finset.range p, (v ((i:ℤ)+1) - v i) = v p - v 0 := by
    induction p with
    | zero => simp
    | succ p ih => rw [Finset.sum_range_succ,ih,Nat.cast_add_one]; abel
  unfold stair; split
  next h => simp_rw [Finset.mul_sum,hu,hp, Int.natAbs_of_nonneg h]
  next h =>
    rw [mul_neg,Finset.mul_sum]; simp only [hu]
    rw [← Finset.sum_neg_distrib]; simp only [Int.negSucc_eq,neg_sub, show ∀ i : ℤ,-(i+1)+1=-i from fun i => by omega]
    exact (hp (fun i => u (-i)) n.natAbs).trans (by simp; rw [abs_of_neg (lt_of_not_ge h),neg_neg])
lemma stair_norm (u : ℤ → ℂ) (n : ℤ) {C} (hu : ∀ b : ℤ, b.natAbs ≤ n.natAbs → ‖u b‖ ≤ C) : ‖stair u n‖ ≤ n.natAbs*C := by
  have he (v : ℕ → ℤ) (hv : ∀ i < n.natAbs,(v i).natAbs ≤ n.natAbs) : ‖∑ i ∈ Finset.range n.natAbs,u (v i)‖ ≤ n.natAbs*C :=
    (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _ => C) (fun i hi => hu (v i) (hv _ (Finset.mem_range.mp hi)))).trans_eq (by simp))
  unfold stair; split
  · exact he _ fun i hi => by simpa using hi.le
  rw [norm_neg]; exact he _ fun i hi => Nat.succ_le_of_lt hi

def dividedMode (i : Axis) (v : Cover) (p : Momentum) := stair (fun b => mode p (Function.update v i b)) (v i)
lemma dividedMode_mult (i : Axis) (v : Cover) (p : Momentum) : q p i * dividedMode i v p = mode p v - mode (mask i p) v := by
  rw [mask_mode]; refine (stair_mult _ (fun b => ?_) (v i)).trans (by rw [Function.update_eq_self])
  rw [show Function.update v i (b+1) = Function.update v i b + step i by ext1 j; by_cases h : j=i <;> simp [*],mode_shift, factor,q]; ring
lemma dividedMode_diff (i : Axis) (v : Cover) : ContDiff ℂ ω (dividedMode i v) := by
  unfold dividedMode stair; split
  · exact ContDiff.sum fun b _ => mode_global _
  exact (ContDiff.sum (s:=Finset.range _) (f:=fun b => fun p => mode p (Function.update v i (Int.negSucc b))) (fun b _ => mode_global _)).neg
lemma dividedMode_period (i : Axis) (v z : Cover) (p : Momentum) : dividedMode i v (p+reciprocal z) = dividedMode i v p := by simp only [dividedMode, mode_phase,mode_periodic,mul_one]
lemma dividedMode_norm (hη : 0<η) (hp : p∈Tube (η/2)) (i : Axis) (v : Cover) : ‖dividedMode i v p‖ ≤ 2/η * Real.exp (η*size v) := by
  refine (stair_norm _ _ (C:=Real.exp (η/2*size v)) (fun b hb => (reward _ _ _ (fun j => (hp j).le)).trans (Real.exp_monotone (by gcongr; exact mask_size i v hb)))).trans ?_
  exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.single_le_sum (f:=fun j => (v j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))) (Real.exp_pos _).le).trans (size_exp_bound v hη)

def divided (i : Axis) (f : Momentum → ℂ) (p : Momentum) := ∑' v, dividedMode i v p * market f 0 v
def divisionCost (η C : ℝ) := 2/(η/3) * (C*(2*((1+η/3)/(η/3)))^(Fintype.card Axis))
variable (i : Axis) (h : Vane f η) (hb : ∀ p∈ Tube η, ‖f p‖≤C)
include h hb
lemma division_bill (hp : p∈Tube (η/6)) : RG.SumBudget (fun v => ‖dividedMode i v p * market f 0 v‖) (divisionCost η C) := by
  have hη := h.side
  have hW := h.issues hb (η/3) (η/3) (by positivity) (by positivity) (by linarith)
  have hm := hW.2.1.mul_left (2/(η/3))
  have he v := mul_le_mul_of_nonneg_right (dividedMode_norm (show 0<η/3 by positivity) (by rwa [show η/3/2=η/6 by ring]) i v) (norm_nonneg (market f 0 v))
  have he v : ‖dividedMode i v p * market f 0 v‖ ≤ _ := (norm_mul ..).le.trans ((he v).trans_eq (mul_assoc ..))
  have hs := Summable.of_nonneg_of_le (fun v => norm_nonneg _) he hm
  exact ⟨fun _ => norm_nonneg _,hs, (hs.tsum_le_tsum he hm).trans (by rw [tsum_mul_left, divisionCost]; gcongr; exact hW.2.2)⟩
lemma division_diff (hp : p∈Tube (η/6)) : ContDiffAt ℂ ω (divided i f) p := by
  obtain ⟨r,hr,he⟩ := Metric.isOpen_iff.mp (Work.F07.stripOpen (η/6)) p hp
  have hη := h.side
  have hW := h.issues hb (η/3) (η/3) (by positivity) (by positivity) (by linarith)
  exact (Work.F02.analytic_series (fun v z => dividedMode i v z * market f 0 v) hr (fun v => ((dividedMode_diff i v).mul contDiff_const).differentiable (by simp))
    (hW.2.1.mul_left (2/(η/3))) (fun v z hz => by rw [norm_mul,← mul_assoc]; gcongr; apply dividedMode_norm (by positivity); rw [show η/3/2=η/6 by ring]; exact he hz)).contDiffAt
omit h hb in
lemma division_period (v : Cover) : divided i f (p+reciprocal v) = divided i f p := by simp only [divided,dividedMode_period]
lemma division_bound (hp : p∈Tube (η/6)) : ‖divided i f p‖ ≤ divisionCost η C := by have he := division_bill i h hb hp; exact (norm_tsum_le_tsum_norm he.2.1).trans he.2.2
lemma division_mult (hp : p∈Tube (η/6)) : q p i * divided i f p = f p - f (mask i p) := by
  rw [divided,← tsum_mul_left]; simp only [← mul_assoc,dividedMode_mult,sub_mul]; rw [Summable.tsum_sub]
  · rw [show ∀ p∈Tube η, ∑' v, mode p v * market f 0 v = f p from h.paints hb, show ∀ p∈Tube η, ∑' v, mode p v * market f 0 v = f p from h.paints hb] <;> try exact tube_mono (by linarith [h.side]) (mask_tube i hp)
    exact tube_mono (by linarith [h.side]) hp
  all_goals
    have he := h.issues hb (η/3) (η/3) (by linarith [h.side]) (by linarith [h.side]) (by linarith [h.side]); apply (he.series _ ?_).2.1.of_norm
    intro j; exact ((tube_mono (show η/6 ≤ η/3 by linarith [h.side]) (by first | exact hp | exact mask_tube i hp)) j).le
end YM.Push.Loops
