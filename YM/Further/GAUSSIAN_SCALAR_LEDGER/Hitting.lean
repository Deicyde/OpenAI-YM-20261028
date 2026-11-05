import YM.Further.GAUSSIAN_SCALAR_LEDGER.Entries
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Threshold
import YM.Progress.STATIONARY_SCENES.Frames

set_option warningAsError false

/-!
# Budgets on local determinant labels reaching a target

Apply before any log interaction. Value norms on scalar, and one sqrt
release for the coefficients of the quadratic precision correction.
Even sum the V-independent envelopes, per site and all orders of the
chain. Here `Filed` is only a geometry price; caller to retain true
label eligibility and dependencies and must pay this invoice at the
native sites specified. No implication that the matrix estimates alone
justify *using* restricted supports for every label.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Trail

open Matrix Function Filter MeasureTheory Set Precision SectorNext.Vacuum Lattice
open YM.Progress.StationaryScenes.Green
open YM.Push.Uniform (Multiplicity Decay countCost count_pos decay_pos)
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {ι : Type*} [Fintype ι] {n : Side}



def encounter (p : Expense) (γ : ℝ) := (p.counts:ℝ)*countCost γ



omit [Fintype ι] in
lemma steep_half (l : ι → Site n) (γ : ℝ) (m : ℕ) (i : ι) (f : Fin m → ι) (j : ι) :
    Real.sqrt (stamp l γ m i f j) = stamp l (γ/2) m i f j := by
  have hh (i j) : Real.sqrt (Decay γ (l i) (l j))=Decay (γ/2) (l i) (l j) := by
    have hk : Decay γ (l i) (l j)=Decay (γ/2) (l i) (l j)^2 := by
      unfold Decay; rw [pow_two,← Real.exp_add]; congr 1; ring
    rw [hk,Real.sqrt_sq (decay_pos ..).le]
  induction m generalizing i with
  | zero => exact hh ..
  | succ k ih =>
    unfold stamp; rw [Real.sqrt_mul (decay_pos ..).le, ih, hh]



variable {χ : ℕ → Type*} [∀ k, Fintype (χ k)]

def Filed (B M N : ℕ) (l : ι → Site n) (X : (k : ℕ) → ι → χ k → Support n) :=
    ∀ k i j x, x∈X k i j → separation x (l i) ≤ (k+2)*M ∧ coverNumber B (X k i j) ≤ (k+2)*N



-- elementary anchor count: don't lose period factor, count every
-- duplicate *position*, not every field value.




def depart (p : Expense) (a C q : ℝ) (M N : ℕ) :=
  let L := Real.exp (a*N)
  (p.counts:ℝ)* ((2*(M:ℝ)+1)^4*16) * (L*C) * (q*L) / (1-16*(q*L))



def boost (a z : ℝ) (N : ℕ) := 16*z*Real.exp (a*N)
def stem (p : Expense) (r : ℝ) := p.windowCost r*encounter p p.margin
def spoke (p : Expense) (r : ℝ) := p.correctionCost r*encounter p p.margin
def root (p : Expense) (r : ℝ) := Real.sqrt (p.correctionCost r)*encounter p (p.margin/2)

structure Books (p : Expense) (r a : ℝ) (N : ℕ) : Prop where
  ready : Timing p r
  book : boost a (stem p r) N < 1/2
  phi : boost a (spoke p r) N < 1/2
  ρ : boost a (root p r) N < 1/2



-- For example does not pay logarithm label derivative costs.


-- M permits B factors per hop. Numerical prices of using such
-- supports are explicit, polynomial in M here.

end YM.Further.GaussianScalar.Trail
