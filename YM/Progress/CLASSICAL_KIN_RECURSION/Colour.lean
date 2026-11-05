import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import YM.PCalc.Band
import YM.Progress.CLASSICAL_KIN_RECURSION.Merge

set_option warningAsError false

/-!
# Coefficients really in the G-invariant color basis

Global conjugation test on the actual jets then use the physical unbounded
periods. Afterwards all constructions act directly on the invariant subspace.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Spools
open Lattice RG Laurent Exterior
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {J : Type} [Fintype J] [DecidableEq J] {n : Side}

def paintSet (q : Tones J G.ColorIndex) (v : J → G.Color) :=
    ∑ b, q b*∏ i,v i (b i)
variable (G J) in
def varnish : Submodule ℝ (Tones J G.ColorIndex) where
  carrier := { q | ∀ g : G.El, ∀ v, paintSet q (fun i => G.adjoint g (v i)) = paintSet q v }
  zero_mem' := by simp [paintSet]
  add_mem' := fun {a b} h g x v => by
    have he (v : J → G.Color) : paintSet (a+b) v=paintSet a v+paintSet b v := by simp [paintSet,add_mul,Finset.sum_add_distrib]
    rw [he,he,h x,g x]
  smul_mem' t a := fun h x v=> by
    have he (v : J → G.Color) : paintSet (t • a) v=t*paintSet a v:= by
      simp [paintSet,Finset.mul_sum,mul_assoc]
    rw [he,he,h x]
variable (G J) in
abbrev Coat := ↥(varnish G J)
variable (G) in
def Stained (u : Voices J G.ColorIndex) := ∀ S x,(u S).val x ∈ varnish G J

section
variable (S : J→Finset Axis) (p : J→Site n)


end

def reflects (r : ℕ) (n : Side) (g : G.El) (v : fieldDir G n r) : fieldDir G n r := fun x => G.adjoint g (v x)


end YM.Progress.ClassicalKin.Spools
