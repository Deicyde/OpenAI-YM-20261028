import YM.Extraction.Lipschitz
import YM.Cells.Certificate

/-!
# Torus-specific replicated primary bounds and packing scales

The centered demand refers to the *whole* tiled product.

Along an extraction use ε-slack after fixing period scale; no uniformity in
number of arrays (one bound incl all copies).

The same constant and power work
as m increases; for each m and volume period sufficiently far along extraction
need cutoffs sufficiently fine allowed to depend on p,m.

Do not call that additional uniformity without a producer.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Cells
open Function Set Filter MeasureTheory
open Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius ComplexOrder
variable {G : Gauge}

def half (S : Schedule) (m p : ℕ) : Side := ⟨(S.side m p).val / 2, by
  apply Nat.div_pos (show 2 ≤ _ from (le_trans (by norm_num) (show 4 ≤ _ from Nat.le_of_dvd (S.side m p).property (S.side_four m p)))) (by norm_num)⟩

lemma original (S : Schedule) (m p : ℕ) : (S.side m p).val = 2*(half S m p).val := by
  have := S.side_four m p; dsimp [half]; omega

/-- Translate tiling so that initial cell is *centered* at cutoff site o.
Use odd subdivision from level m. -/
def center (S : Schedule) {m N : ℕ} (p : ℕ) (h : m ≤ N) (o : Site (S.side N p)) : Tiling (S.side N p) where
  period := S.side m p
  units := S.toDepth h p
  widthHalf := half S m p
  even := original S m p
  kind := .link
  base := fun i => o i - (((S.toDepth h p).count.val/2 : ℕ) : Per (S.side N p))

lemma trueLength (S : Schedule) {m N p : ℕ} (h : m ≤ N) (o) :
    S.a N * (center S p h o).side.val = S.a m := S.embeds_scale (S.toDepth h p)

lemma root_fraction (S : Schedule) {m N p : ℕ} (h : m ≤ N) (o) :
    (Fintype.card (center S p h o).Cell : ℝ)⁻¹ = (S.a m / (S.period p).val)^4 := by
  rw [site_card]; dsimp only [center]
  rw [← S.span_side m p]; have hx := S.a_pos m
  push_cast; field_simp

lemma base_point (S : Schedule) {m N p : ℕ} (h : m ≤ N) (o) : o ∈ (center S p h o).chamber 0 := by
  intro i
  rw [Tiling.starts_zero]
  let r := S.toDepth h p
  have hp : r.count.val ≤ (S.side N p).val := calc
    _ ≤ (S.side m p).val * r.count.val := le_mul_of_one_le_left (Nat.zero_le _) (S.side m p).property
    _ = _ := r.exact_size.symm
  change (o i - (o i - ((r.count.val/2 : ℕ) : Per _))).val < r.count.val
  rw [sub_sub_cancel]
  have hL : 0 < r.count.val := r.count.property
  rw [ZMod.val_natCast_of_lt (by omega)]; omega

/-- Points from fixed (possibly distinct) grid levels. N-positions pad by
origin whenever too coarse. -/
def location (S : Schedule) (k N p : ℕ) (x : Cover) : Site (S.side N p) :=
  if h : k ≤ N then (S.toDepth h p).embed (wrap _ x) else 0

structure CellHyp (C : Family G) (f : Extraction.Order) : Prop where
  all (N p) : Seam G (C.side N p) (C.beta N p)
  /-- also all sufficiently fine m and all labels in a fixed
  bounded multiplet; we use sup-norm balls by grade bound & explicit ε slack at each m.
  Exact direction copies already encoded by rootTest. Larger fixed constants
  with no `ε` for a chosen rational power can follow. `A` here independent
  of m. -/
  centered (d : ℕ) (ε R : ℝ) (hε : 0 < ε) (hr : 0 < R) : ∃ m₀ : ℕ, C.ref d ≤ m₀ ∧
    ∃ A : ℝ, 0 ≤ A ∧ ∀ m ≥ m₀, ∀ η : ℝ, 0 < η → f.late fun N p => ∃ h : m ≤ N,
      ∀ v : C.book.Ref d, ‖v‖ ≤ R → ∀ x : Site (C.side N p),
        Interior ((center C.S p h x).chamber 0) (C.O N p (d := d) v x) ∧
        (center C.S p h x).rootTest (C.beta N p) (C.O N p (d := d) v x) ≤ A * (C.S.a m) ^ (-(d:ℝ)-ε) + η

theorem seamless {C : Family G} (H : C.Makes) (N p : ℕ) : Seam G (C.side N p) (C.beta N p) :=
  laws _ _ _ <| by
    have ht := (H.wilson.represents N p N le_rfl).band.1
    exact le_trans (div_nonneg (zero_le_one.trans (C.path.levels.fits.delayed N).le) (by norm_num)) ht

theorem recur {C : Family G} {f : Extraction.Order} (h : CellHyp C f) (g : Extraction.Order) :
    CellHyp C (f.refine g) := by
  refine ⟨h.all,?_⟩; intro d ε R he hr
  obtain ⟨m,hv,A,ha,H⟩ := h.centered d ε R he hr
  exact ⟨m,hv,A,ha,fun M hm i hi => Extraction.Order.late_refine f g (H M hm i hi)⟩
end YM.Cells
