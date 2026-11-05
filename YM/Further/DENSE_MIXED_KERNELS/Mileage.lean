import YM.Further.DENSE_MIXED_KERNELS.Word

/-!
# Allocation of one joint component's derivative cost

Grows polynomially in the actual total size, period-independent. Commit
parameters before buying other pre/post-L parts; exact numbers for
application stay hypotheses. Counting old kernel polynomial losses once
on each operand—not once per forest or once per marker of a mode. Use
with any of the pre-L extra cover exponent reservations needed by the
remaining tests (System then reserves seven in its step method).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Finset MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian Surface
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
namespace Mileage
variable {G : Gauge} {A : ChartRatio G} (H : Port A) {s j z d k : ℕ} {T : ℝ}

def supply (j : ℕ) : ℝ := (2 + 4*(j:ℝ))^j * Real.exp 1
lemma supply_one (j) : 1 ≤ supply j := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by
  have : 0≤(j:ℝ) := Nat.cast_nonneg _; linarith)) (Real.one_le_exp zero_le_one)

lemma expense_le (ht : 1≤T) (hh : (d:ℝ) ≤ T) : expense d j T⁻¹ ≤ supply j*T^(2*j) := by
  have he := zero_lt_one.trans_le ht
  have h : 2+(j:ℝ)/(T⁻¹/(2*(1+(d:ℝ)))) ≤ (2+4*(j:ℝ))*T^2 := by
    rw [show (j:ℝ)/(T⁻¹/(2*(1+(d:ℝ)))) = j*(T * 2 * (1+(d:ℝ))) by field_simp]
    have hi : T * 2 * (1+(d:ℝ)) ≤ T*2*(2*T) := by gcongr; linarith
    nlinarith only [mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg j),one_le_pow₀ ht (n:=2)]
  unfold expense supply; rw [pow_mul,mul_right_comm _ (Real.exp 1),← mul_pow]; gcongr

-- Separate naming for the constants (used prior to seeing the word length).
def distance (k : ℕ) := 2 + 4*k
def orderPrice (k q : ℕ) := distance k * k + 2*((q+2)*k*2)
def marks (H : Port A) (k : ℕ) := pen H k 1 + 3^k*(2^k*supply (2*k)) + (2:ℝ)^k*(1+4*curve H k 1)

lemma marks_pos (k : ℕ) : 0 ≤ marks H k := by
  have hx : 0 ≤ pen H k 1 := pen_pos H k zero_le_one
  have hj : 0 ≤ curve H k 1 := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  have hv := supply_one (2*k); unfold marks; positivity
lemma curve_price (k : ℕ) (T : ℝ) : curve H k T = curve H k 1 * T := by unfold curve; ring
lemma pen_price (k : ℕ) (T : ℝ) : pen H k T = pen H k 1 * T := by unfold pen curve; ring

lemma tally_spot (ht : 1 ≤ T) (hz : (z:ℝ) ≤ T) (hd : (d:ℝ) ≤ T) :
    tally H z d k T T⁻¹ T ≤ marks H k * T^distance k := by
  have hp := zero_lt_one.trans_le ht
  have hS : T^2 ≤ T^distance k := pow_le_pow_right₀ ht (by unfold distance; omega)
  have hC : 0 ≤ curve H k 1 := mul_nonneg (zero_le_one.trans (H.cash k)) (by positivity)
  have he : 0 ≤ pen H k 1 := pen_pos H k (t:=1) zero_le_one
  unfold marks tally; rw [add_mul (_+_),add_mul (pen H k 1)]
  apply add_le_add (add_le_add ?_ ?_) ?_
  · apply (mul_le_mul_of_nonneg_right hz (pen_pos H k hp.le)).trans; rw [pen_price H k T]
    nlinarith only [mul_le_mul_of_nonneg_left hS he]
  · rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (show 0≤(3:ℝ)^k by positivity)
    unfold stall; apply (mul_le_mul_of_nonneg_left (expense_le (j:=2*k) ht hd) (by positivity : 0 ≤ 2^k*T*T)).trans_eq
    unfold distance; ring_nf
  rw [curve_price H k T]
  nlinarith only [mul_le_mul_of_nonneg_left hS (show 0≤(2:ℝ)^k*(1+4*curve H k 1) by positivity)]

def license (k q : ℕ) (H : Port A) := (2+marks H k)^k*(2+supply ((q+2)*k*2))
lemma license_pad (k q : ℕ) : 3 ≤ license k q H := by
  have hp := marks_pos H k; have ht := supply_one ((q+2)*k*2)
  apply le_trans (b:=2+supply _) (by linarith)
  exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by linarith))

lemma pay (k q : ℕ) (ht : 1 ≤ T) (hz : (z:ℝ) ≤ T) (hd : (d:ℝ) ≤ T) (hs : (s:ℝ) ≤ T) :
    billed H s z d k q T T⁻¹ T ≤ license k q H * T^orderPrice k q := by
  unfold billed license orderPrice
  let v := tally H z d k T T⁻¹ T
  have hv : 0 ≤ v := tally_pos H _ _ _ (by positivity) (by linarith) (by linarith)
  let m := (q+2)*k*2
  have hE : 0 ≤ marks H k := marks_pos H _
  have hC : 0 ≤ flight H s z d k T T⁻¹ T := by unfold flight; change 0 ≤ _+v; positivity
  rw [pow_add]; change (flight ..)^k * (2+expense d m T⁻¹) ≤ (_*(2+supply m))*(T^(distance k*k)*T^(2*m))
  rw [show T^(distance k*k)=(T^distance k)^k from pow_mul T (distance k) k,mul_mul_mul_comm, ← mul_pow]; apply mul_le_mul
  · apply pow_le_pow_left₀ hC _
    have hh := tally_spot (k:=k) H ht hz hd
    unfold flight; have he := mul_le_mul_of_nonneg_right hs (show 0 ≤ T by linarith)
    nlinarith only [he,hh, show T^2 ≤ T^distance k from pow_le_pow_right₀ ht (by unfold distance; omega), one_le_pow₀ ht (n:=distance k)]
  · nlinarith only [expense_le (j:=m) ht hd,one_le_pow₀ ht (n:=2*m)]
  · have he := expense_ge (inv_pos.mpr (zero_lt_one.trans_le ht)) d m; linarith
  positivity

variable {α : Type}

/-- Size is NONZERO per address, including repeated copies. Use from
old fine input cover (or old halo query), and from vacuum-owned addresses
including packet multiplicities as needed. -/
def totSize (x : Chain α) (size : α→ℕ) := ∑ i,size (x.2 i)
def transom (C : ℝ) (r : ℕ) (x : Chain α) (size : α→ℕ) := C * (1+(totSize x size :ℝ))^r

def shift (k q r d : ℕ) (C : ℝ) := (license k q H * C^orderPrice k q)*(1+(d:ℝ))^(r*orderPrice k q)

lemma enough_length (x : Chain α) (r : ℕ) (hr : 0<r) (size : α→ℕ) (he : ∀ i,0<size i) {C : ℝ} (hC : 1 ≤ C) :
    (Fintype.card x.Index:ℝ) ≤ transom C r x size := by
  have hs : Fintype.card x.Index ≤ totSize x size := by
    simpa [totSize,Chain.Index] using Finset.sum_le_sum (f:=fun _=>1) (s:=Finset.univ) (g:=fun i=>size (x.2 i))
      fun i _ => show 1≤size _ from he _
  let V := totSize x size; have hv : 1 ≤ 1+(V:ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg _)
  calc
    _ ≤ (V:ℝ) := Nat.cast_le.mpr hs
    _ ≤ 1+(V:ℝ) := le_add_of_nonneg_left zero_le_one
    _ ≤ (1+(V:ℝ))^r := by exact
      (show _=(1+(V:ℝ))^1 from (pow_one _).symm).le.trans (pow_le_pow_right₀ hv hr)
    _ ≤ _ := le_mul_of_one_le_left (by positivity) hC

lemma shift_pad (k q r d : ℕ) {C : ℝ} (hC : 1≤C) : 3≤ shift H k q r d C := by
  have hp := license_pad H k q
  refine hp.trans ((le_mul_of_one_le_right (by linarith) (one_le_pow₀ (n:=orderPrice k q) hC)).trans ?_)
  exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by exact le_add_of_nonneg_right (by positivity)))

private lemma sum_part {ι : Type*} (s : Finset ι) (f : ι→ℝ) (h : ∀ i,0≤f i) : 1+∑ i∈s,f i ≤ ∏ i∈s,(1+f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj,prod_insert hj]
    apply le_trans _ (mul_le_mul_of_nonneg_left ih (by linarith [h j]))
    nlinarith [Finset.sum_nonneg (s:=s) (f:=f) (fun i _ => h i),h j]

lemma receipt (k q r : ℕ) (x : Chain α) (size : α→ℕ) {C : ℝ} (hC : 1≤C) : license k q H *
    transom C r x size ^ orderPrice k q ≤ ∏ i,shift H k q r (size (x.2 i)) C := by
  let L := license k q H; let P := orderPrice k q
  have hx : 1 ≤ L := le_trans (by norm_num : (1:ℝ)≤3) (license_pad ..)
  have hK : 1≤ L*C^P := one_le_mul_of_one_le_of_one_le hx (one_le_pow₀ hC)
  unfold transom shift
  change L*(C*_ )^P ≤ ∏ i,L*C^P*_
  rw [Finset.prod_mul_distrib, Finset.prod_const, mul_pow,←pow_mul,←mul_assoc (a:=L)]
  apply mul_le_mul
  · apply le_trans (pow_one (L*C^P)).symm.le (pow_le_pow_right₀ hK ?_)
    simp only [card_univ, Fintype.card_fin]; omega
  · rw [Finset.prod_pow]
    apply pow_le_pow_left₀
    · positivity
    unfold totSize; push_cast; exact sum_part _ (fun i => (size (x.2 i):ℝ)) (fun _ => Nat.cast_nonneg _)
  · positivity
  positivity
end Mileage
end YM.Further.DenseMixedKernels
