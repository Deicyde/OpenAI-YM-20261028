import YM.Push.STRESS_FLUX.Haar
import YM.Push.STRESS_FLUX.Low

/-!
Jacobian charge in the clover Ward identity. Keep the actual matrix Casimir
in the Wilson representation (not assumed scalar on the representation).
For nonwrapping elementary faces (actually side ≥ 2 suffices), it is itself a
diagonal local difference, NOT dropped. Distinct from conservation of the
whole tensor. Supplies quantitative pointwise control and a potential improved
discrete prescription.
-/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Jacobian
open Function Set Gauge Lattice Wilson RG
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff InnerProductSpace
variable {G : Gauge} {n : Side} {C : Family G} {p N : ℕ}

def loop (U : Config G n) (x : Site n) (a b : Step) := travel U x (Lattice.oriented a b)

def quad (c : G.Color) (u : G.El) := - (G.colorMat c * (G.colorMat c * G.mat u)).trace.re / G.repDim
def lap (u : G.El) := ∑ i : G.ColorIndex, Jacobian.quad (orth i : G.Color) u
@[simp] lemma quad_inv (c : G.Color) (u : G.El) : Jacobian.quad c u⁻¹ = Jacobian.quad c u := by
  let X := G.colorMat c
  have ht : (star (X*(X*G.mat u))).trace.re = (X*(X*G.mat u)).trace.re := by rw [Matrix.star_eq_conjTranspose, Matrix.trace_conjTranspose]; rfl
  rw [star_mul,star_mul,show star X=-X from G.colorMat_skew c,mul_neg,mul_neg,neg_mul,neg_neg,Matrix.mul_assoc, Matrix.trace_mul_comm,Matrix.mul_assoc] at ht
  exact congr_arg (fun z : ℝ => -z / G.repDim) (G.mat_inv u ▸ ht : (X*(X*G.mat u⁻¹)).trace.re=(X*(X*G.mat u)).trace.re)
@[simp] lemma lap_inv (u : G.El) : lap u⁻¹ = lap u := by simp [lap]



lemma cycle (U : Config G n) (x : Site n) (a b : Step) : loop U x a b =
    a.read U x * b.read U (x+a.vec) * (a.read U (x+b.vec))⁻¹ * (b.read U x)⁻¹ := by
  rw [loop,Lattice.oriented]; simp only [travel,mul_one]; rw [Step.vec_rev,show x+a.vec+b.vec+-a.vec=x+b.vec by abel,
    Step.read_rev,add_right_comm x a.vec b.vec,Step.read_rev]; group





















def bill (U : Config G n) (x : Site n) (a b : Axis) := lap (loop U x (posDir a) (posDir b)) + lap (loop U x (negDir a) (posDir b))









def marker (U : Config G n) (x : Site n) (b : Axis) : ℝ := (8:ℝ)⁻¹ * ∑ a ∈ Finset.univ.erase b, (Jacobian.bill U x a b - 2*lap (G:=G) 1)




@[fun_prop] lemma continuous_marker (x : Site n) (b : Axis) : Continuous (fun U : Config G n => marker U x b) := by
  unfold marker Jacobian.bill lap quad loop; fun_prop


end YM.StressFlux.Jacobian
