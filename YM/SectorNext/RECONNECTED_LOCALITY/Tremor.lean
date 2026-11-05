import YM.SectorNext.RECONNECTED_LOCALITY.Crust

set_option warningAsError false

/-!
k=0 pass to E mass, uses sqrt Schur (charge after roots, retain
coordinates & repeated addresses). d and halos COST in output L units.
Peak fibres & native halo price, no use of finite periodic volume factor
nor finite rooted cyclic count. Useful also for determinant routes. Calls
`WEATHER` separately since position-block price is paid at half rate, on
blocks (not colors). Produce constants after label cover reserves, EXP/B
small. Address scatter along route avoids even poly(nB)^4 at root in E.
This file fixed length.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Function Filter Matrix Finset Lattice RG Wilson Bind Window
open scoped BigOperators
variable {I : Type*} [Fintype I] {c:Side}

def Hail (u : I→Site c) (ν : ℝ) (L : ℝ) (i j : I) := L * Real.exp (-ν*(separation (u i) (u j)))
variable {u : I→Site c} {ν L D E k a b : ℝ}

omit [Fintype I] in
lemma down (i j : I) (h : 0≤L) : 0≤Hail u ν L i j := mul_nonneg h (Real.exp_pos _).le





def zone (u : I→Site c) (P : ℕ) := ∀ x,(univ.filter (fun i=>u i=x)).card ≤ P





/-- Products for routes, permitting separate chain and terminal prices
(e.g. S & A). -/
def fee (F H : I→I→ℝ) : (n : ℕ) → Logs I n → ℝ
  | 0,l => H l.1 l.2.2
  | n+1,(x,h,t) => F x (h 0) * fee F H n (h 0,Fin.tail h,t)

variable {F H : I→I→ℝ}
omit [Fintype I] in
lemma fee_nonneg (hf : ∀ i j,0≤F i j) (hh : ∀ i j,0≤H i j) (n : ℕ) (q : Logs I n) : 0≤fee F H n q := by
  induction n with
  | zero => exact hh ..
  | succ n ih => rcases q with ⟨i,e,j⟩; exact mul_nonneg (hf ..) (ih _)




end YM.SectorNext.Reconnect.Ice
