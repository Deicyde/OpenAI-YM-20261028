import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct

/-!
# Reflected equation valves

Check directly that the unnormalized proposal with averaged vector fields
under `pull` achieves the average of J as *functions*. Includes when `flip`
forces neg link, uses no change of density beyond Wilson symmetries already
proved. Independent of transfers. `RWardBin` etc need BOTH formula and prices
and their own equivariance scopes at visited stencils & offsets; this is only
for exact calibration on signed symmetrizations.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProjectorNext.Calibration
open Lattice Wilson RG Source Function Tensor Work Labels Next.Foundations Push.CutoffProjectors
open scoped Topology Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {n : Side} (s : Signed)





abbrev Native (n : Side) := Edge (Site n)

def mapSite : Equiv.Perm (Native n) := Equiv.ofBijective (sendEdge s 0) ⟨sendEdge_injective s 0,
    Finite.injective_iff_surjective.mp (sendEdge_injective s 0)⟩

/-- Color transform carrying an increment at the image positive edge, back
to an increment in configurations being used by unaveraged stencil. -/
def basisBack (U : Config G n) (e : Native n) : Module.End ℝ G.Color :=
    if s.flip e.2 then -(G.adjoint (U (mapSite s e))⁻¹) else LinearMap.id







/-- Encode vector fields as real-linear color functionals, to include generic
real/complex inserts and avoid introducing a complex color frame. -/
abbrev MachineFields (G : Gauge) (n : Side) := Config G n → Native n → G.Color →ₗ[ℝ] ℂ

namespace MachineFields
variable {X : MachineFields G n}

def whisk (X : MachineFields G n) : MachineFields G n := fun U e =>
    let l := (mapSite s).symm e
    (X (pull s 0 U) l).comp (basisBack s U l)

def flight {K : Type*} (f : Config G n → K) (U : Config G n) (e : Native n) (c : G.Color) (t : ℝ) :=
    f (increment U (t • oneEdge e c))

def AlongD (X : MachineFields G n) : Prop := ∀ (U : Config G n) (e : Native n) (u : G.Color),
    DifferentiableAt ℝ (fun v => X (increment U v) e u) 0

abbrev rate (U : Config G n) (e : Native n) (c u : G.Color) (X : MachineFields G n) :=
    deriv (flight (fun V => X V e c) U e u) 0

lemma AlongD.fly (h : AlongD X) (U : Config G n) (e : Native n) (c u : G.Color) :
    HasDerivAt (flight (fun V => X V e c) U e u) (rate U e c u X) 0 := by
  let d := oneEdge e u
  have he : DifferentiableAt ℝ (fun t : ℝ => t • d) 0 := by
    exact differentiableAt_id.smul_const d
  have hh : DifferentiableAt ℝ (fun v => X (increment U v) e c) ((0:ℝ) • d) := by rw [zero_smul]; exact h ..
  exact (hh.comp 0 he).hasDerivAt



 -- cruise gets rewritten by backwards?







end MachineFields
end YM.ProjectorNext.Calibration
