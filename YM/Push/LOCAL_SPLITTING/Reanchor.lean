import YM.Push.LOCAL_SPLITTING.Funding
import YM.Push.LOCAL_SPLITTING.Padding
import YM.Push.LOCAL_SPLITTING.RelocateGas



/-!
# Re-anchor a complete singleton source without translating the observable

Unlike a matched symmetry move, this needs to merge old forced marks, pay
true support/weight shifts, and can change the coordinates. New read about
`b` with actual section; every density uses the original unmarked Rep. This
API takes a +2 support reserve at input, costs pre-side for bounded native
separation. No inference of this extra reserve from bare `.remBound` (which
by itself only asks for its one exponent), no applicability assertion to
comparing different RG block hierarchies without further estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Local.Reanchor
open Function Filter Lattice Wilson RG Source Labels Next.Foundations Work.G08
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}

section Geometry



def exchange (N : ℕ) (B : BudgetPoint) := ((1+(N:ℝ))^B.power)^B.order






end Geometry

def Extra (B : BudgetPoint) (o : Site n) (R : Rep G n) (P : Coefficient F n) (a b : ℝ) :=
    (∃ e : ℕ → ℝ, (∀ i, B.supBounds o (P.support i) (P.regular i) (e i)) ∧ SumBudget (fun i => reservedMass B (P.support i) (e i)) a) ∧
    ∃ e : ℕ → ℝ, (∀ i, 0 ≤ e i ∧ ∀ U, ‖P.forced i U‖ ≤ e i) ∧ SumBudget (fun i => reservedMass B (patch R.activities i) (e i)) b

namespace Extra
variable (T : SectionData F) (o : Site n) (R : Rep G n) (P : Coefficient F n) in
def components : ℕ → Config G n → ℂ
  | 0 => presented T o R.p.threshold (F.core P.x)
  | i+1 => P.regular i

variable (T : SectionData F) (o : Site n) (P : Coefficient F n) in
def sites : ℕ → Support n
  | 0 => T.footprint o
  | i+1 => P.support i

variable {A : Hol G} {T : SectionData F} {o : Site n} {R : Rep G n} {P : Coefficient F n}










end Extra

open Extra

section Transport
variable (T : SectionData F) (o b : Site n) (R : Rep G n) (L : Nonempty (Reserve R.activities))
    (P : Coefficient F n)

def enlarge (i : ℕ) := insert b (sites T o P i)
def extended (i : ℕ) := insert b (patch R.activities i)

def defect (i : ℕ) := masked R.p.threshold (sites T o P i) (components T o R P i) - masked R.p.threshold (enlarge T o b P i) (components T o R P i)

def moved : Raw F n where
  seed := P.x 0 • F.e0
  bulk := components T o R P
  forced := (slots L (extended b R)).collect R.p.threshold P.forced + (slots L (enlarge T o b P)).pack R.p.threshold (defect T o b R P)

variable (A : Hol G) in
def tune := (moved T o b R L P).build b (enlarge T o b P) A T R (slots L (fun i => joint T b (enlarge T o b P i)))

variable {R L T o P} {A : Hol G} {w v a c : ℝ} {N : ℕ}

















end Transport
end YM.Push.Local.Reanchor
