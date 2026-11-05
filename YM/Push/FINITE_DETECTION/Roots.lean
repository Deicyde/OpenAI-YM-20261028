import YM.Next.BOUNDARY.Alias
import YM.Push.FINITE_DETECTION.Test

/-!
# Sufficient corrected all-copy input on the actual aligned pair rows

before continuum rank, *use* the small rooted corrected
cylinders to obtain the ordinary moment comparison. This is the subset
calculation for one row with TWO physical slots (incl. two copies of the same
label). No independence assumption. Free constant for the pair subtraction
is the **second cumulant at actual rounded rescaled positions**.
No uncentered knot-turning or R×N uniformity needed by our lemma. This does
not construct the small-root budgets, nor use `RankWidths` or `Trials.Valid`
(which has other requirements too). Also an elementary rounding estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.FiniteDetection
open Lattice Cells Wilson MeasureTheory Dash Extraction Next.Extract Function Set Filter
open scoped Topology BigOperators

variable {G : Gauge}
section Budget
variable {n : Side} {p q : Config G n → ℂ} {β : ℝ} {a b z δ : ℂ}

def minus (a : ℂ) (p : Config G n → ℂ) := fun u => p u - a

def corrected (p q : Config G n → ℂ) (a b c : ℂ) := fun u => minus a p u * minus b q u - (c-a*b)

variable {Δ : ℝ} {T : Tiling n}
structure Budget (T : Tiling n) (β : ℝ) (p q : Config G n → ℂ) (a b z : ℂ) (Δ : ℝ) : Prop where
  left : Interior (T.chamber 0) p
  right : Interior (T.chamber 0) q
  cost_left : T.rootTest β (minus a p) ≤ Δ
  cost_right : T.rootTest β (minus b q) ≤ Δ
  cost_pair : T.rootTest β (corrected p q a b z) ≤ Δ






end Budget

variable {C : Family G} {d : ℕ} {f : Extraction.Order}
def scaledGrid (C : Family G) (k : ℕ) {n : ℕ} (u : Fin n → Cover) (r : ℝ) := r⁻¹ • Order.grid C k u





def atGrid (C : Family G) (k : ℕ) (s : Cover) (d : ℕ) (u : ℕ×ℕ) (v : C.label d) : Config G (C.side u.1 u.2) → ℂ :=
  C.O u.1 u.2 (d := d) v (location C.S k u.1 u.2 s)



def pointOne (x : E4) (v : Model C d) := (Standard C).useAt (Standard C) (points fun _ : Fin 1 => x) (fun _ => ⟨d,v⟩)


variable {ι : Type*}
def Paid (β : Module.Basis ι ℂ (Model C d)) (f : Extraction.Order) (depth : ℕ → ℕ) (mark : ℕ → Fin 2 → Cover)
    (r gap : ℕ → ℝ) (ξ : ℕ → ℕ×ℕ → ι → C.label d) := ∀ᶠ k : ℕ in atTop, ∀ ε : ℝ, 0 < ε → ∀ᶠ u : ℕ×ℕ in f.fuse,
      let y := scaledGrid C (depth k) (mark k) (r k)
      ∃ T : Tiling (C.side u.1 u.2), ∀ i j : ι, Budget T (C.beta u.1 u.2)
        (atGrid C (depth k) (mark k 0) d u (ξ k u i)) (atGrid C (depth k) (mark k 1) d u (ξ k u j))
        (pointOne (y 0) (β i)) (pointOne (y 1) (β j)) (pointPair C d y (β i) (β j)) (gap k + ε)




end YM.Push.FiniteDetection
