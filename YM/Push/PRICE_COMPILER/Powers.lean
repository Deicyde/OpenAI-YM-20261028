import YM.Push.PRICE_COMPILER.Post

/-!
# Example after-L power requests actually installable via the compiler

Here price one-time arbitrary fixed-L powers of Λ (both stages on an
edge), by p to an arbitrary small **positive** exponent per transition.
θ chosen to meet these powers too. Include an example use commissioning
both this and the grant exponential conversion (Suppression) simultaneously.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.PriceCompiler
open Filter Function Lattice RG RG.Supply Wilson Precision Pressure
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge}

/-- List maxima/sums per usable edge can go here. -/
structure PowerBill where
  degree : ℕ → ℕ → ℕ
  cost : ℕ → ℕ → ℝ
  small : ℕ → ℕ → ℝ
  cost_pos i j : 0 < cost i j
  positive i j : 0 < small i j

namespace PowerBill
variable (p : PowerBill)







/-- Also β delay needed, enough to absorb the constant powers even as
costs increase between stages. -/
def extra (j i : ℕ) (x : ℝ) := p.cost j i * 8^(p.degree j i) ≤ mon x ^ (p.small j i / 2)




end PowerBill

section Installation
variable {P : Before} {f : ℕ → ℕ} {D : Rolls (P.sheet G f)} (M : Preparations P D)



variable {M}

end Installation
end YM.Push.PriceCompiler
