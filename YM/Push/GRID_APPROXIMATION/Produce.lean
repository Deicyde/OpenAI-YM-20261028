import YM.Next.BOUNDARY.Synchronize
import YM.Push.GRID_APPROXIMATION.Cover
import YM.Push.GRID_APPROXIMATION.Palette

/-!
# Grill and AtGrid conditional on pre-integration signed RG estimates

Precise difference from assuming existence of plots comparing to pair
products: uses full-array represented-dependent signal estimates at finite
cutoffs, calculated in the same histories, see Candidates.lean
(`Supplies`). These are requests about B70's actual quantitative densities --
not assuming occupancy, validity of a many-source construction, frame
retuning, spare marker supports etc from the fact one has a Seed. The work
uses fixed-degree requests BEFORE word sizes are known. Retain everything
across arbitrary further refinements. Both fixed-order service and
AtGrid-style port with Seed and per-demand actual refinement support.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Function Filter Set Cells OS Next.BOUNDARY
open scoped Topology BigOperators

variable {G : Gauge}

/-- Single direction request per degree ≤ d, at one common
h-grid.

Already needs estimates on joint arrays to supply (product over all
copies at h).

Estimates at stop, after true signed propagation.

No other
context (e.g.

IR basis data) free to change. -/
def MixAt (C : Family G) (f : Extraction.Order) (d h : ℕ) :=
    ∀ (j : ℕ), j ≤ d → ∀ i : Ind C j, i≠0 → Supplies C f h (swatch C j i)



/-- Version with arbitrary further-order service, Seed optionally
available as in AtGrid. The further station order q after h here can be
used for All mix estimates at this h, retained through every n,x,g;r.
Does not ask `Π` bounds at arbitrarily high weights once d is fixed. -/
def AtMaterials (C : Family G) (f : Extraction.Order) (S : Table C.book) :=
    ∀ p : Extraction.Order, Spec.Seed C (f.refine p) S → ∀ d m : ℕ,
      ∃ h ≥ m, ∃ q : Extraction.Order, MixAt C ((f.refine p).refine q) d h

variable {C : Family G} {f g : Extraction.Order} {d h n : ℕ}

lemma figures_all (H : C.Makes) (hm : MixAt C f d h) :
    ∃ Z : ∀ j ≤ d, ∀ i : Ind C j, Figures C (swatch C j i) h,
      (∀ (j : ℕ) (hj : j ≤ d), Z j hj 0 = onePaint C j h) ∧
      ∀ (j : ℕ) (hj : j ≤ d) (v : C.label j), star v=v → (palette (Z j hj) v).Gives f := by
  choose Z hZ hz using fun (j : ℕ) (hj : j ≤ d) => paints H f j h (hm j hj)
  exact ⟨Z, hZ, fun j hj => palette_gives (Z j hj) H (hz j hj)⟩

/-- A cover result at real, simply injective positions, including Θ
comparison. The given budgets are for the SAME finite palette for all
monomial arities, not reselected with x. -/
lemma from_palette (H : C.Makes) (Z : ∀ j ≤ d, ∀ i : Ind C j, Figures C (swatch C j i) h)
    (he : ∀ (j : ℕ) (hj : j ≤ d) (v : C.label j), star v=v → (palette (Z j hj) v).Gives f)
    (v : Fin n → C.book.Token) (hv : ∀ i, (v i).fst ≤ d) (hp : Grid.plain (C:=C) v)
    (x : Fin n → Cover) (hx : Injective x) :
    ∃ P : Grid.Covering (C:=C) h v x, P.Works h v x f := by
  have hm (u : Fin n → C.book.Token) (hr : ∀ i, (u i).fst ≤ d) (hh : Grid.plain (C:=C) u) :
      let Q := fun i => palette (Z (u i).fst (hr i)) (u i).snd
      ∀ i, Figures.Gives (v:=u i) (Q i) f := fun i => he (u i).fst (hr i) (u i).snd (hh i)
  have hu : Grid.plain (C:=C) (flipTokens v) := by
    intro i
    change star (C.book.mirrorGroup _ _ (v i).2) = _; rw [Register.star_mirror,hp i]; rfl
  have h1 := hm v hv hp
  have h2 := hm (flipTokens (C:=C) v) hv hu
  exact ⟨cover x _ _ h1 h2,covers x _ _ h1 h2 H hx⟩

lemma plots (H : C.Makes) (hm : MixAt C f d h) (x : Fin n → Cover) : PlotBounds C f d h n x := by
  obtain ⟨Z,hZ,he⟩ := figures_all H hm
  intro hx v hv hp
  apply from_palette H Z he v hv hp x
  intro i j h
  apply hx timeAxis
  unfold Extraction.Order.grid
  simp only [points_apply,h]










end YM.Push.GridApprox
