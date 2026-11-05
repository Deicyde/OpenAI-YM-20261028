import YM.Further.GAUSSIAN_SCALAR_LEDGER.Rates

set_option warningAsError false

/-!
# Unwind local errors into individually bounded ordered scalar labels

No color regroup needed. Here there ARE many labels even for a single
matrix entry of a power; want uniform summability against physical
metrics for the determinant remainders not just norm convergence of the
matrix sum. Keep all path displacements & E pulse integral.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Trail

open Matrix Function Filter MeasureTheory Set Precision SectorNext.Vacuum Lattice
open Round (rowRate)
open RawPrice (tear)
open YM.Progress.StationaryScenes.Green
open YM.Push.Uniform (Multiplicity Decay countCost count_pos decay_pos)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : Side}

def tread (X Y : Wall ι) : ∀ m : ℕ, ι → (Fin m → ι) → ι → ℝ
  | 0, i, _, j => Y i j
  | m+1, i, f, j => X i (f 0)* tread X Y m (f 0) (Fin.tail f) j

-- `bill` on total distance traveled, including repeated positions

def stamp (l : ι → Site n) (γ : ℝ) : ∀ m : ℕ, ι → (Fin m → ι) → ι → ℝ
  | 0, i, _, j => Decay γ (l i) (l j)
  | m+1, i, f, j => Decay γ (l i) (l (f 0)) * stamp l γ m (f 0) (Fin.tail f) j

omit [Fintype ι] [DecidableEq ι] in
lemma stamp_pos (l : ι → Site n) (γ : ℝ) (m : ℕ) (i : ι) (f : Fin m → ι) (j : ι) :
    0 < stamp l γ m i f j := by
  induction m generalizing i with
  | zero => exact decay_pos ..
  | succ k ih => exact mul_pos (decay_pos ..) (ih _ _)

omit [DecidableEq ι] in
lemma bound_tread {l : ι → Site n} {A B γ : ℝ} (X Y : Wall ι) (hX : Double l γ A X) (hY : Double l γ B Y)
    (h : 0≤A) (m : ℕ) (i : ι) (f : Fin m → ι) (j : ι) : |tread X Y m i f j| ≤ A^m* B * stamp l γ m i f j := by
  have ht (V : Wall ι) (C : ℝ) (H : Double l γ C V) (i j : ι) : |V i j| ≤ C*Decay γ (l i) (l j) := by
    apply le_of_mul_le_mul_left _ (wt_pos γ (l i) (l j)); refine (Double.point H i j).trans_eq ?_
    unfold Decay wt; rw [mul_left_comm,← Real.exp_add,neg_mul,add_neg_cancel,Real.exp_zero,mul_one]
  induction m generalizing i with
  | zero => rw [tread,stamp,pow_zero,one_mul]; exact ht _ _ hY ..
  | succ k ih =>
    rw [tread,abs_mul]; refine le_trans (mul_le_mul (ht X A hX i (f 0)) (ih _ _)
      (abs_nonneg _) (mul_nonneg h (decay_pos ..).le)) ?_
    exact le_of_eq (by rw [pow_succ,stamp]; ring)

lemma wheels (X Y : Wall ι) (m : ℕ) (i j : ι) : ∑ f, tread X Y m i f j = (X^m*Y) i j := by
  induction m generalizing i with
  | zero => simp [tread]
  | succ k ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ => ι))] -- orientation
    rw [Fintype.sum_prod_type]; simp_rw [tread]
    rw [pow_succ',mul_assoc,Matrix.mul_apply]; refine Finset.sum_congr rfl fun b _ => ?_
    rw [← ih]; simp [Finset.mul_sum,Fin.consEquiv]

omit [DecidableEq ι] in
lemma steam (l : ι → Site n) (γ : ℝ) (hγ : 0 < γ) (K : ℕ) (h : Multiplicity l K) (m : ℕ) (i : ι) :
    ∑ j, ∑ f, stamp l γ m i f j ≤ (K * countCost γ)^(m+1) := by
  induction m generalizing i with
  | zero => simpa [stamp] using h.count l hγ (l i)
  | succ k ih =>
    let C := K*countCost γ
    rw [Finset.sum_comm, ← Equiv.sum_comp (Fin.consEquiv (fun _ => ι)), Fintype.sum_prod_type]
    have hp b : ∑ j,∑ f,stamp l γ k b f j ≤ C^(k+1) := ih b
    calc
      _ ≤ ∑ b : ι, Decay γ (l i) (l b)* C^(k+1) := by
        refine Finset.sum_le_sum fun b _ => ?_
        apply le_trans _ (mul_le_mul_of_nonneg_left (hp b) (decay_pos ..).le)
        rw [Finset.sum_comm]; exact le_of_eq (by simp [stamp,Finset.mul_sum,Fin.consEquiv])
      _ ≤ C^(k+1+1) := by rw [← Finset.sum_mul,pow_succ' _ (k+1)]; exact mul_le_mul_of_nonneg_right (h.count l hγ (l i)) (by unfold C; have hv := count_pos hγ; positivity : 0 ≤ C^(k+1))

section sheets

variable {p : Expense} {A : Wall ι} {l : ι → Site n} (Z : Lens ι) {r : ℝ}


-- transpose used here just to enumerate from the right.


omit [Fintype ι] [DecidableEq ι] in
private lemma tread_cts (X Y : ℝ → Wall ι) (h : ContinuousOn X (Ioi 0)) (he : ContinuousOn Y (Ioi 0))
    (m : ℕ) (i : ι) (f : Fin m → ι) (j : ι) : ContinuousOn (fun u => tread (X u) (Y u) m i f j) (Ioi 0) := by
  induction m generalizing i with
  | zero => exact continuousOn_pi.mp (continuousOn_pi.mp he i) j
  | succ m ih => exact (continuousOn_pi.mp (continuousOn_pi.mp h i) (f 0)).mul (ih _ _)
























end sheets
end YM.Further.GaussianScalar.Trail
