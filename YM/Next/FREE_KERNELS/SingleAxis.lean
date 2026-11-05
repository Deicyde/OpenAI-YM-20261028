import YM.Next.FREE_KERNELS.Stock
import YM.Next.FREE_KERNELS.Tariff

/-!
# A Laurent monomial divided by one exterior multiplier

`partAxis` uses finite interval sums with sign even when the coefficient
sits far out on the negative part of the cover. The length cost is paid by
the original (larger) positive exponent. Not a pointwise quotient at
harmonic momentum.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Free
open Filter Set Function Lattice Laurent Bloch Metric Exterior Matrix Precision RG Work.F08
open scoped Topology BigOperators ComplexConjugate

/-- Price the telescope starting at integer b and terminating at b+n. -/
def intervalAxis (k : Axis) (x : Cover) (b : ℤ) (n : ℕ) (i : Cover) :=
    ∑ l ∈ Finset.range n, token (Function.update x k (b+l)) i

def zeroAxis (k : Axis) (x : Cover) := token (Function.update x k 0)

def partAxis (k : Axis) (x : Cover) (i : Cover) := if 0≤x k then intervalAxis k x 0 (x k).natAbs i else -intervalAxis k x (x k) (x k).natAbs i

lemma eval_axis (η : ℝ) (hp : 0≤η) (k : Axis) : Tariff (zeroAxis k) η η 1 := fun i => by
  unfold zeroAxis; rw [one_mul]; apply (token_rate ..).mono le_rfl; unfold envelopeW; exact Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast step_size i k 0 (by simp)) hp)
lemma interval_sum (η : ℝ) (hp : 0≤η) (k : Axis) (x : Cover) (b : ℤ) (n : ℕ)
    (h : ∀ l : ℕ, l<n → (b+l).natAbs ≤ (x k).natAbs) : Width η (n*envelopeW η x) (intervalAxis k x b n) := by
  induction n with
  | zero => simp [intervalAxis,Laurent.Width, SumBudget]
  | succ n ih =>
    have he := ih fun a ha => h a (by omega)
    have hh : Width η (envelopeW η x) (token (update x k (b+n))) := (token_rate _ η).mono le_rfl (Real.exp_monotone
        (mul_le_mul_of_nonneg_left (by exact_mod_cast step_size x k _ (h n (by omega))) hp))
    convert! Width.add_line he hh using 1
    · push_cast; ring
    funext i; unfold intervalAxis; rw [Finset.sum_range_succ]

lemma dividend (η : ℝ) (hp : 0<η) (k : Axis) : Tariff (partAxis k) η (η/2) (η/2)⁻¹ := by
  intro x
  let θ := η/2; have ht : 0<θ := by unfold θ; linarith
  let m := (x k).natAbs
  have hh : Width θ ((m:ℝ)*envelopeW θ x) (partAxis k x) := by
    unfold partAxis
    by_cases hx : 0 ≤ x k <;> simp only [hx, if_true,if_false]
    · apply interval_sum θ ht.le; intro l hl; omega
    have hb := interval_sum θ ht.le k x (x k) m (fun l hl => by unfold m at *; omega)
    simpa only [norm_neg,norm_one,neg_mul,one_mul] using Width.scale_line (-1) hb
  apply hh.mono le_rfl
  have he : (m:ℝ) ≤ size x := by unfold size; exact_mod_cast Finset.single_le_sum (f:=fun i => (x i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  have hm : θ*m ≤ θ*size x := mul_le_mul_of_nonneg_left he ht.le
  change (m:ℝ)*envelopeW θ x ≤ θ⁻¹*envelopeW η x
  unfold envelopeW
  have ha := Real.add_one_le_exp (θ*size x)
  have hc : Real.exp (η*size x)=Real.exp (θ*size x)*Real.exp (θ*size x) := by rw [← Real.exp_add]; unfold θ; congr 1; ring
  rw [hc,← mul_assoc]; exact mul_le_mul_of_nonneg_right (by rw [inv_mul_eq_div, le_div_iff₀ ht]; linarith) (Real.exp_pos _).le

lemma interval_signal (k : Axis) (x : Cover) (b : ℤ) (n : ℕ) {p : Momentum} (hp : physical p) :
    q p k*RRead (intervalAxis k x b n) p = mode p (update x k (b+n))-mode p (update x k b) := by
  have hh (z : ℤ) : mode p (update x k (z+1))-mode p (update x k z)=q p k*mode p (update x k z) := by rw [step_one,mode_shift,Exterior.factor]; unfold Exterior.q; ring
  unfold intervalAxis; rw [real_sum _ _ hp]; swap
  · exact fun i _ => (((token_rate _ 0).unweighted le_rfl).2.1)
  simp_rw [token_eval]; rw [Finset.mul_sum]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih,← hh]; push_cast; rw [← add_assoc b]; ring
lemma part_signal (k : Axis) (x : Cover) {p : Momentum} (hp : physical p) :
    q p k*RRead (partAxis k x) p = mode p x-mode p (update x k 0) := by
  let y := x k
  unfold partAxis
  by_cases h : 0≤x k <;> simp only [h,if_true,if_false]
  · rw [interval_signal _ _ _ _ hp,show (0:ℤ)+(x k).natAbs=x k by omega, Function.update_eq_self]
  rw [RRead_neg, mul_neg,interval_signal _ _ _ _ hp,show x k+((x k).natAbs:ℤ)=0 by omega, Function.update_eq_self]; ring

lemma shift_axis (k : Axis) (x : Cover) (p : Momentum) : mode p (update x k 0)=mode (update p k 0) x := by
  unfold mode; congr! 2
  apply Finset.sum_congr rfl; intro i _; by_cases h : i=k <;> simp [Function.update,h]
lemma retreat_axis (k : Axis) (x : Cover) (p : Momentum) : RRead (zeroAxis k x) p=mode (update p k 0) x := by rw [zeroAxis,token_eval,shift_axis]
lemma retuned {u : Cover → ℝ} {η C : ℝ} (h : Width η C u) (he : 0<η) (k : Axis) {p : Momentum} (hp : physical p) :
    RRead (payOut (zeroAxis k) u) p=RRead u (update p k 0) := by
  rw [(eval_axis η he.le k).redeemed zero_le_one h he.le hp]
  simp_rw [retreat_axis]; unfold RRead Laurent.read; exact tsum_congr fun i => mul_comm ..
lemma real_blank {p : Momentum} (hp : physical p) (k : Axis) : physical (update p k 0) := by
  rw [physical_iff] at *; intro i; by_cases h : i=k <;> simp [Function.update,h,hp]
lemma bank_blank {p : Momentum} (hp : p∈baseCube) (k : Axis) : update p k 0 ∈ baseCube := by
  refine ⟨real_blank hp.1 _,fun i => ?_⟩; by_cases h : i=k
  · simp [h,Real.pi_pos.le]
  simpa only [Function.update_of_ne h] using hp.2 i
lemma single_axis {u : Cover → ℝ} {η C : ℝ} (h : Width η C u) (he : 0<η) (k : Axis) {p : Momentum} (hp : physical p) :
    q p k*RRead (payOut (partAxis k) u) p=RRead u p-RRead u (update p k 0) := by
  rw [(dividend η he k).redeemed (by positivity) h (by positivity) hp,← tsum_mul_left]
  unfold RRead Laurent.read; simp only [smul_eq_mul]
  have hh := (h.unweighted he.le).2.1
  rw [← (real_series hh hp).tsum_sub (real_series hh (real_blank hp k))]
  refine tsum_congr fun i => ?_
  change q p k * ((u i:ℂ)*RRead (partAxis k i) p) = _
  rw [mul_left_comm,part_signal _ _ hp,shift_axis]
  ring
end YM.Next.Free
