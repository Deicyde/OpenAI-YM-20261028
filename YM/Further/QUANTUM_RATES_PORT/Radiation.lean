import YM.Extra.ITERATION_NO_LOSS.Spectrum
import YM.Further.QUANTUM_RATES_PORT.Symbols

set_option warningAsError false
/-!
# Momentum-side normalizations for `traceTest`

Unfold against `K'`, Laurent curvature kernel and link-momentum fibers.
Invoice can thus use just the **opposite complex momentum mixed**
coefficient, before serialization, on those fibers. This translation doesn't
need Ward estimates. Keep the curvature symbol HALF of the residual
precision, symmetrize if needed, and average the actual signed path
channels. If working with a different base (e.g., midpoint phases in a
comparison on part of the complex strip), the producer still has to bring
the symbols back to THESE conventions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.QuantumRates.Fiber
open Function Filter Lattice Wilson RG Precision Exterior Tree  Bid Bloch Finset Matrix Laurent
open Extra.Iteration  Waves
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {G : Gauge} {n : Side}





/-- Linear orientation pulls into the full canonical signed channel. -/
def color (s : Signed) : Waves.Field G n →ₗ[ℂ] Waves.Field G n where
  toFun x i b :=
    let p := (posDir (axisEquiv.symm i.2)).rotate s
    let u := p.used (affine s 0 i.1)
    if p.neg then -x (u.1,coord u.2) b else x (u.1,coord u.2) b
  map_add' x y := by funext i b; dsimp only [Pi.add_apply]; split <;> simp [add_comm]
  map_smul' z x := by funext i b; dsimp only [Pi.smul_apply]; split <;> simp







open Kernels

def pick (s : Signed) (b : PlaqAxes) (j : G.ColorIndex) (w : Site n) : Waves.Field G n →ₗ[ℂ] ℂ where
  toFun V := amplitude (fun x : Site n => fpoint (color s V) j (x,plaquette b)) w
  map_add' x y := by unfold amplitude; simp only [map_add, fpoint_add, Pi.add_apply, mul_add,sum_add_distrib]
  map_smul' t x := by
    unfold amplitude; simp only [map_smul, fpoint_smul,Pi.smul_apply, smul_eq_mul,RingHom.id_apply,Finset.mul_sum]
    apply sum_congr rfl; intro i _; ring







def folded (u : Symbol G 2) (s : Signed) : Waves.Field G n →ₗ[ℂ] Waves.Field G n →ₗ[ℂ] ℂ where
  toFun v := {
    toFun w := (n.val:ℂ)^4 * ∑ p : Fin 2 → Site n,
      if (∑ i,p i)=0 then ∑ i : Shape 2,∑ b : Hue G 2, u i b (phase p) *
        (pick s (i 0) (b 0) (p 0) v * pick s (i 1) (b 1) (p 1) w) else 0
    map_add' x y := by
      simp only [map_add,mul_add,mul_sum,mul_ite,mul_zero, ← sum_add_distrib]
      apply sum_congr rfl; intro p _; split
      · simp only [sum_add_distrib]
      ring
    map_smul' t x := by
      simp only [map_smul,RingHom.id_apply,mul_sum,mul_ite,mul_zero]; rw [smul_sum]
      apply sum_congr rfl; intro p _; split
      · simp only [mul_sum,smul_eq_mul]; refine sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      simp }
  map_add' x y := by
    apply LinearMap.ext; intro z
    simp only [LinearMap.add_apply,LinearMap.coe_mk,AddHom.coe_mk,map_add,add_mul,mul_add,mul_sum,
      ← sum_add_distrib,mul_ite,mul_zero]; apply sum_congr rfl; intro p _; split
    · simp only [sum_add_distrib]
    ring
  map_smul' t x := by
    apply LinearMap.ext; intro z
    simp only [LinearMap.smul_apply,RingHom.id_apply,LinearMap.coe_mk,AddHom.coe_mk,map_smul,smul_eq_mul,mul_sum,mul_ite,mul_zero]
    apply sum_congr rfl; intro p _; split
    · exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
    ring





/-- Symmetrization with no extra precision factor. -/
def branch (u : Symbol G 2) : Waves.Field G n →ₗ[ℂ] Waves.Field G n →ₗ[ℂ] ℂ :=
    (Fintype.card Signed:ℂ)⁻¹ • ∑ s : Signed,(2:ℂ)⁻¹ • (folded u s + (folded u s).flip)

















end YM.Further.QuantumRates.Fiber
