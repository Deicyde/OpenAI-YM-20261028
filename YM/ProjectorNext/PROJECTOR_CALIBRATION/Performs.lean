import YM.ProjectorNext.PROJECTOR_CALIBRATION.Average
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Backwards
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Cylinders


/-!
# Performing a Brand certification at the valves

Include `Packet.X` slot scaling when paying the contract. Use `reflects`
for genuinely differentiated raw mirror sum; all on the same N,p (even
outside where using with a nonwrapping ledger). And exact J orientation.
No assumption that chain receipts can be met after averaging! -/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice RG Wilson Source Function Tensor Work Labels Next.Foundations Push.CutoffProjectors MachineFields Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d : ℕ}
namespace Machine
variable (M : Machine C.params d)

/-- Unscaled (x takes slots directly). -/
def assembly (N p : ℕ) : (C.labels.level d).Coeff →ₗ[ℂ] MachineFields G (C.side N p) :=
    let f (k : (C.labels.level d).Index) (U : Config G (C.side N p)) (e : Edge (Site _)) : G.Color →ₗ[ℝ] ℂ :=
      ∑ i : M.Outlet, if e=M.port 0 i then M.valveL _ k i (expandAt 0 U) else 0
    ∑ i, LinearMap.toSpanSingleton ℂ _ (f i) ∘ₗ LinearMap.proj i

variable {N p : ℕ}





/-- Deployed signed vector field as components. All group assignments on
true links. No x_N matched values in the constructor. -/
def audit (N p : ℕ) : (C.labels.level d).Coeff →ₗ[ℂ] Vectors G (C.side N p) where
  toFun x U e j := share * ∑ s : Signed, whisk s (M.assembly N p (turn (C.labels.level d) s⁻¹ x)) U e (colors G j)
  map_add' x y := by
    funext U e j
    simp only [map_add, whisk, Pi.add_apply, LinearMap.comp_apply,LinearMap.add_apply,Finset.sum_add_distrib,mul_add]
  map_smul' t x := by
    funext U e j
    simp only [map_smul, whisk, Pi.smul_apply, LinearMap.comp_apply,LinearMap.smul_apply,smul_eq_mul,← Finset.mul_sum]
    simp; ring

variable (E : Packet C d N p)




end Machine
end YM.ProjectorNext.Calibration
