import YM.Corona.Fit
import YM.Next.EXTRACTION.Tails
import YM.Next.SCHEDULE.Melt


/-! Use B70 *connected-cover* costs for retained atom supports. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter Lattice RG Wilson MeasureTheory 
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical

variable {n m L : Side} {q : Ratio m n} {r : ℕ} {B P : BudgetPoint} {X : Support n} {o : Site n}

/-- Retain projected positions of FULL one-time reads. -/
def positions (q : Ratio m n) (X : Support n) := (inspected X).image q.parent
/-- This halo is the expenditure ceiling, not inserted over an already
paid `Y` and not over the fitted section. Payload's own indicator halos
still required. -/
def skirt (P : BudgetPoint) (r : ℕ) (q : Ratio m n) (X : Support n) := halo (r * P.B) (X.image q.parent)




def Small (B : BudgetPoint) (L : Side) (X : Support n) := (coverNumber B.B X)^3 ≤ L.val
lemma Small.cost (h : Small B L X) : coverNumber B.B X ≤ L.val := by
  let s := coverNumber B.B X
  by_cases he : s=0
  · change s ≤ _; rw [he]; omega
  exact le_trans (le_self_pow₀ (a:=s) (Nat.pos_of_ne_zero he) (by decide)) h

lemma Small.tight (h : Small B q.count X) (hx : o∈X) (hp : B.B ≤ 2*P.B)
    (hs : 4≤q.count.val) (hT : 100*(P.B+1) ≤ m.val) : Nonwrapping X o := by
  let s := coverNumber B.B X
  have he : 2*s ≤ q.count.val := by
    by_cases ha : s < 2
    · omega
    refine le_trans ?_ h
    change _ ≤ s^3
    rw [pow_succ]; gcongr; nlinarith only [ha]
  intro x ht
  have hv : separation x o ≤ s*(10*P.B) + 4*P.B := by
    apply (Corona.extent X B.B ht hx).trans
    exact Nat.add_le_add (Nat.mul_le_mul_left _ (by have := P.B_pos; omega)) (by omega)
  have h : 2*s*P.B ≤ q.count.val*P.B := Nat.mul_le_mul_right _ he
  have hh := Nat.mul_le_mul_right q.count.val hT
  rw [q.exact_size]; nlinarith only [hv,h,hh,P.B_pos,hs]

/-- Pre-length back-trade gate. -/
def toll (r : ℕ) : ℕ := ((r+6)+(r+6)+1)^ (4:ℕ)
def phaseBase (r : ℕ) (p : ℝ) := (p+2)*(toll r:ℝ)
def Across (B P : BudgetPoint) (r : ℕ) (L : Side) :=
    20*phaseBase r P.supportExponent ≤ (L.val:ℝ)*B.supportExponent

def quote (P : BudgetPoint) (a : Support m) := (P.supportExponent+2) * coverNumber P.B a


/-- Width units beyond the principal halo; subtraction is in ℝ. Keeps
sensitivity to full support also for wrapping labels. -/
def relative (P : BudgetPoint) (C Y : Support m) (w : ℝ) := Real.exp (quote P Y - quote P C) * w




/-- Delay condition pays fine-direction pre-mask supports only, not the
whole volume. -/
def umbrella (B : BudgetPoint) (L : Side) := L.val * (4*B.B+2) + 2*B.B + 8
def Umbered (B : BudgetPoint) (L : Side) := B.threshold * (1+(umbrella B L:ℝ))^B.power ≤ 1

end YM.Planned.AtomRegular
