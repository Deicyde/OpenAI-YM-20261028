import YM.Extra.ITERATION_NO_LOSS.Kernels

/-!
# Per-period identification for emitted tensors

Counts all sites. Frequencies at actual integer mesh points. Value on real
paired waves later includes mixed polarizations and cancellations; no estimate
on (say) holomorphic values near aliased singularities is inferred by this
evaluation step.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Kernels
open Filter Function Lattice Wilson RG Exterior Precision Laurent Bloch Complex Finset Bid
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {k : ℕ}

def phase (p : Fin k → Site n) : Momenta k := fun j => mon (p j.1) j.2




def amplitude (v : Site n → ℂ) (p : Site n) := ((n.val:ℂ)^4)⁻¹ * ∑ x : Site n, (cell p x)⁻¹ * v x


def starts (V : Flux G n) (i : Shape k) (b : Hue G k) (j : Fin k) := amplitude (fun x => (V (i j) (b j) x:ℂ))
def pay (V : Flux G n) (i : Shape k) (b : Hue G k) (p : Fin k → Site n) := ∏ j, starts V i b j (p j)





variable {K : Kernel G k}






end YM.Extra.Iteration.Kernels
