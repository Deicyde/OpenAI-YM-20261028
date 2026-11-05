import YM.Cells.Corrected
import YM.Push.CORRECTED_COLUMNS.Positions
import YM.Push.CORRECTED_COLUMNS.Stretch

/-!
# Simultaneous admissible placement of every test from fixed columns

Strictly anti lengths without assuming monotonicity of (mesh*monitor^b)
through all changes of parameters.

Same J.

Works before any extraction or
choice of coefficients and can use sufficiently high stages.

We specialize to the right-closed rounding and allow further
thinning; producers should use this same placement geometry in all the
required bills.

`fitData` after buying enough room; use with numerical
lemma `Zone.enough`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected
open RG Lattice Cells Extraction Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G) {S : Table C.book} {d : ℕ}

section
open Zone
abbrev lvl := C.path.levels
/-- The available k-series. -/
structure Series where
  depth : Sequence
  b : ℝ
  b0 : 0 < b
  h (k : ℕ) : Allows (lvl C) b (depth k)
  forward : StrictMono (fun k => base (lvl C) b (depth k))
  decreasing : StrictAnti (fun k => scale (lvl C) b (depth k))


end
namespace Series
variable {C}
def further (B : Series C) (t : Sequence) : Series C :=
  ⟨B.depth.after t,B.b,B.b0,fun k => B.h (t k),B.forward.comp t.monotone,B.decreasing.comp_strictMono t.monotone⟩

abbrev side (B : Series C) : Sequence := ⟨_,B.forward⟩
lemma side_le (B : Series C) (k : ℕ) : B.side k ≤ B.depth k := Nat.sub_le ..
abbrev scale (B : Series C) (k : ℕ) := Zone.scale (lvl C) B.b (B.depth k)
abbrev inversePitch (B : Series C) (k : ℕ) := Zone.gain (lvl C) B.b (B.depth k)
lemma scale_pos (B : Series C) (k : ℕ) : 0 < B.scale k := Zone.positive ..


variable (B : Series C) {n : ℕ}

-- Put down all slot marks in this initial cell
-- (still checking fit, not claiming through arbitrary logs).
def address (k : ℕ) (x : Points n) := Extraction.address (B.inversePitch k)⁻¹ x

def site (k : ℕ) (x : Points n) := Order.grid C (B.depth k) (B.address k x)
def rescaled (k : ℕ) (x : Points n) := (B.scale k)⁻¹ • B.site k x
lemma rescale (k : ℕ) (x : Points n) : B.rescaled k x= Extraction.tag (B.inversePitch k)⁻¹ (B.address k x) := by
  let a := B.scale k
  have ht := C.S.a_pos (B.depth k)
  have hw : 0<B.inversePitch k := Zone.pointed ..
  ext1 i; ext1 j
  change (C.S.a (B.depth k)* B.inversePitch k)⁻¹*(C.S.a (B.depth k)* _) = _⁻¹ * ((B.address k x i j : ℤ):ℝ)
  field_simp

lemma tuned (h : G.Simple) (x : Points n) : Tendsto (fun k => B.rescaled k x) atTop (𝓝 x) := by
  have hp : Tendsto (fun k => (B.inversePitch k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ((Zone.thin _ B.b h B.b0).comp B.depth.cofinal)
  rw [tendsto_iff_dist_tendsto_zero]; simp_rw [rescale]
  refine squeeze_zero (fun k => dist_nonneg) (fun i => approximate (inv_pos.mpr (Zone.pointed ..)) _) ?_
  simpa only [mul_zero] using hp.const_mul (4*n:ℝ)





end Series

variable {C} (X : Columns C S d)

/-- Fit for every slot/basis input/row. -/
def Placed (B : Series C) : Prop := ∀ k i,
    B.site k (X.row i).expected∈generic _ ∧
      ∀ j, Positions.Comfortable C.S (B.side k) (B.depth k) (B.address k (X.row i).expected j)




end YM.Push.Corrected
