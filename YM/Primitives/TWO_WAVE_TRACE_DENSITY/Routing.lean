import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Fourier.AddCircleMulti
import YM.CellFourier.Mesh


/-!
# Routed, bilinear two-wave contractions (C12

Route is an equality in *physical* coordinates. Entry traces keep all cell
slots (including residues/colors, with no implicit dimension factor).
Provides also exact stencil inlet using Bloch convolution and anchor
modulations. Kinematics separately from strip estimates. Compatible-period
arithmetic in Characters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Primitives.TwoWave
open Lattice Laurent Bloch Matrix Complex
open scoped Topology BigOperators ComplexConjugate

variable {n : Side} {α β γ : Type*}

/-- Test on a **complex** wave, positive sign, no site factor. -/
def ray (p : Site n) (v : α → ℂ) : Site n × α → ℂ := fun i => cell p i.1*v i.2

/-- Deals with genuine matrices on the torus. F indexed by INCOMING
frequency. After complexification of jets use matrix product and trace
(no conjugation of the second wave). -/
def Routed [Fintype β] (h : Site n) (A : Matrix (Site n×α) (Site n×β) ℂ) (F : Site n → Matrix α β ℂ) :=
    ∀ (p : Site n) (v : β → ℂ), A *ᵥ ray p v = ray (p+h) (F p *ᵥ v)





















/-- For reciprocal updates of the shifted internal q, with no
representative abuse. -/
lemma mon_add (p t : Site n) : ∃ z : Cover, mon (p+t) = mon p + mon t + reciprocal z := by
  obtain ⟨z,hz⟩ := cover_of_eq (lift p + lift t) (lift (p+t)) (n:=n) (by simp [map_add])
  refine ⟨z,funext fun i => ?_⟩
  simp only [mon, hz, reciprocal,Pi.add_apply,Pi.smul_apply,smul_eq_mul,Int.cast_add,← Nat.cast_smul_eq_nsmul ℤ]
  simp only [Int.cast_mul,Int.cast_natCast]
  field_simp [side_ne]
end YM.Primitives.TwoWave
