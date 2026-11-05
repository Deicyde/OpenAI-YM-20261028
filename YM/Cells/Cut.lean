import YM.Lattice.Subdivision
import YM.Wilson.Symmetry
import YM.Lattice.Support
import Mathlib.Analysis.Complex.Order

/-!
# Tile seams on a native pair of periodic hyperplanes

Line coordinates are ZMod(period at native cutoff). Half is native. Base
line `b` means seam through site b, or link seam *between b-1 and b*. In link tiling the
strict interior of a slab includes sites at distance half a step. In site
tilings do not read transverse links at seams. .
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
open Lattice Wilson

inductive Kind | site | link deriving DecidableEq

namespace Kind

/-- Twice setback before base. -/
def shift : Kind → ℕ
  | site => 0
  | link => 1

/-- coordinate r=x−b from start at b. Strict. -/
def Strict : Kind → ℕ → ℕ → Prop
  | site, w, r => 0 < r ∧ r < w
  | link, w, r => r < w

lemma strict_lt {k : Kind} {w r} (h : k.Strict w r) : r < w := by cases k; exact h.2; exact h
end Kind

variable {n : Side}

structure Cut (n : Side) where
  half : Side
  even : n.val = 2 * half.val
  kind : Kind
  pos : Axis
  baseLine : Per n

namespace Cut
variable (C : Cut n)

/-- Circle coordinates measured from C. -/
def distance (x : Site n) := (x C.pos - C.baseLine).val

@[simp] theorem back (x) : (C.distance x : Per n) = x C.pos - C.baseLine := by simp [distance,Per]

def sector : Set (Site n) := {x | C.kind.Strict C.half.val (C.distance x)}

abbrev flip : Signed := Signed.mirror C.pos
def slide : Site n := (2 * C.baseLine - (C.kind.shift : Per n)) • step C.pos

def reflect (x : Site n) := affine C.flip C.slide x

@[simp] theorem reflect_here (x : Site n) : C.reflect x C.pos = 2*C.baseLine-(C.kind.shift : Per n)-x C.pos := by
  simp [reflect,affine,flip, slide,Signed.mirror,Signed.act]; ring

@[simp] theorem reflect_there (x : Site n) {a : Axis} (h : a ≠ C.pos) : C.reflect x a = x a := by
  simp [reflect,affine,flip,slide,Signed.mirror,Signed.act,h,Ne.symm h]

@[simp] theorem twice (x : Site n) : C.reflect (C.reflect x) = x := by
  funext a; by_cases h : a=C.pos <;> simp [h]

/-- Pull configuration. -/
def pullC (G : Gauge) := pull (K := G.El) C.flip C.slide

@[simp] theorem pulls (G : Gauge) (U : Config G n) : C.pullC G (C.pullC G U)=U := by
  unfold pullC
  have he : affine C.flip C.slide C.slide = C.reflect (C.reflect 0) := by
    rw [show C.reflect 0 = C.slide by simp [reflect,affine]]; rfl
  rw [pull_pull,he,twice,show C.flip*C.flip = 1 from
    calc _ = C.flip⁻¹*C.flip := rfl
         _ = _ := inv_mul_cancel _, pull_id]

lemma zeroLength : (2:Per n) * C.half.val = 0 := by
  rw [← Nat.cast_ofNat (n := 2), ← Nat.cast_mul, ← C.even]; exact ZMod.natCast_self _

/-- Link seams split all sites. -/
theorem link_switch (h : C.kind = .link) {x} (hx : x ∈ C.sector) : C.reflect x ∉ C.sector := by
  change ¬C.kind.Strict _ _
  change C.kind.Strict _ _ at hx
  rw [h] at hx ⊢
  change distance C x < _ at hx
  have hv : C.distance (C.reflect x) = n.val - (C.distance x + 1) := by
    have ha : C.distance x + 1 ≤ n.val := by rw [C.even]; omega
    have hb : n.val - (C.distance x + 1) < n.val := by have := n.property; omega
    rw [← ZMod.val_natCast_of_lt hb]
    change ZMod.val (C.reflect x _ - C.baseLine) = ZMod.val _
    apply congr_arg ZMod.val
    rw [reflect_here, Nat.cast_sub ha,h]
    rw [ZMod.natCast_self,Nat.cast_add,C.back]
    dsimp only [Kind.shift]; ring
  change ¬ C.distance (C.reflect x)<_
  rw [hv, C.even]; omega
end Cut

section Cylinder
variable {G : Gauge}

/-- Strict measurable local assignment with uniform *one-law* bound.
No continuum bound hidden. -/
structure Interior (K : Set (Site n)) (F : Config G n → ℂ) : Prop where
  gauge : GaugeInvariant F
  borel : Measurable F
  localSites : LocalOn K F
  cost : ∃ c : ℝ, ∀ U, ‖F U‖ ≤ c

/-- Endpoint coordinate cut form (equivalent to PSD on families by closing Interior under summing). -/
def Positive (G : Gauge) {n : Side} (β : ℝ) (C : Cut n) : Prop := ∀ F : Config G n → ℂ,
    Interior C.sector F → 0 ≤ moment β (fun U => F U * star (F (C.pullC G U)))
end Cylinder
end YM.Cells
