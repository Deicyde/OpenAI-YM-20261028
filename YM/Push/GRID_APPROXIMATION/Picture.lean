import YM.Next.EXTRACTION.Basis
import YM.Push.GRID_APPROXIMATION.Joint

/-!
# One real actual label being approximated on the given fixed grid

The implementation supplies these *via pre-integration* estimates
(`Candidates`): these intermediate rooted comparison output types themselves
should not be read as having been assumed of the Wilson measures in the
spec. All assertions at ordered tails (plus some stronger finite ports),
not field products in a reconstructed phase. Radius really controls native
dependence (including both link endpoints), also across t/placements via
translation. Center h fixed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.GridApprox
open RG Lattice Wilson MeasureTheory Set Filter Function Cells
open scoped Topology BigOperators ComplexOrder

variable {G : Gauge}

structure PictureAt (C : Family G) (v : C.book.Token) (h N p : ℕ) (Z : Config G (C.side N p) → ℂ)
    (cap err radius : ℝ) : Prop where
  fine : h ≤ N
  calibrated : C.ref v.1 ≤ N
  /-- Original label draw fits too, no uniform sup on it in this field. -/
  source : Interior ((tilesAt C.S p fine).chamber 0) (C.seen v 0)
  target : Interior ((tilesAt C.S p fine).chamber 0) Z
  /-- Physical shrink support, permits padding w=0. -/
  short : ∃ w : ℕ, C.S.a N*w ≤ radius ∧ Interior (window 0 w) Z
  bound U : ‖Z U‖ ≤ cap
  real U : star (Z U)=Z U
  cost : (tilesAt C.S p fine).rootTest (C.beta N p) (Z-C.seen v 0) ≤ err

structure Figures (C : Family G) (v : C.book.Token) (h : ℕ) where
  plot (a N p : ℕ) : Config G (C.side N p) → ℂ
  cap : ℕ → ℝ
  err : ℕ → ℝ
  radius : ℕ → ℝ

namespace Figures
variable {C : Family G} {v : C.book.Token} {h : ℕ} (Z : Figures C v h)

structure Gives (f : Extraction.Order) : Prop where
  plain : star v.2=v.2
  cap_pos q : 0 < Z.cap q
  err_nn q : 0 ≤ Z.err q
  radius_nn q : 0 ≤ Z.radius q
  cost : Tendsto Z.err atTop (𝓝 0)
  shrinks : Tendsto Z.radius atTop (𝓝 0)
  late q : f.late fun N p => PictureAt C v h N p (Z.plot q N p) (Z.cap q) (Z.err q) (Z.radius q)


end Figures

def HasFigures (C : Family G) (v : C.book.Token) (h : ℕ) (f : Extraction.Order) :=
    ∃ Z : Figures C v h, Z.Gives f

/-- A one-cutoff sup bounds the rooted norm irrespective of volume/path.
Use *only* when sup available, e.g. for a single approximant at fixed cost;
not for original high-cutoff cylinders at their given normalization. -/
lemma root_sup {n : Side} (T : Tiling n) (β : ℝ) (F : Config G n → ℂ)
    (h : Interior (T.chamber 0) F) (r : ℝ) (hv : 0 ≤ r) (he : ∀ U, ‖F U‖ ≤ r) :
    T.rootTest β F ≤ r := by
  apply le_of_pow_le_pow_left₀ (T.cells_positive.ne') hv
  rw [T.powering]; unfold Tiling.rootPower moment
  have ht := T.manyIntegral β (fun _ => F) (fun _ => h)
  have hh (U : Config G n) : ‖T.fullAt (fun _ => F) U‖ ≤ r^(Fintype.card T.Cell) := by
    unfold Tiling.fullAt; rw [norm_prod]
    have hx (i : T.Cell) : ‖T.copy i F U‖ ≤ r := by
      unfold Tiling.copy; split <;> simp [he _]
    calc
      _ ≤ ∏ _ : T.Cell, r := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hx i)
      _ = _ := by simp
  exact (norm_integral_le_integral_norm _).trans ((integral_mono ht.norm (integrable_const _) hh).trans (by simp))

/-- One intermediate already suffices for budget on the original *at fixed
h*. Thus we can prove the approximation port conditional without needing an
additional Wcmain port (which would give growth control also to shrinking h).
-/
lemma PictureAt.budget {C : Family G} {v : C.book.Token} {h N p : ℕ} {Z : Config G (C.side N p) → ℂ}
    {cap err radius : ℝ} (H : C.Makes) (e : PictureAt C v h N p Z cap err radius) (hc : 0 ≤ cap) :
    (tilesAt C.S p e.fine).rootTest (C.beta N p) (C.seen v 0) ≤ cap + err := by
  let T := tilesAt C.S p e.fine
  let O : Config G (C.side N p) → ℂ := C.seen v 0
  let W := Z-O
  have hp : Interior (T.chamber 0) W := by
    change Interior _ (Z-O)
    rw [sub_eq_add_neg]
    have hh : Interior (T.chamber 0) (fun U => (-1:ℂ)*O U) := e.source.scale (-1)
    exact e.target.plus (show Interior _ (fun U => -O U) from by simpa using hh)
  have hv : (-W)=(-1:ℂ) • W := (neg_one_smul ℂ W).symm
  have he := (seamless H N p).semi T Z ((-1:ℂ) • W) e.target (hp.scale (-1))
  have hw := Next.Extract.root_smul T (C.beta N p) W (-1)
  have hs : Z+(-1:ℂ) • W=O := by rw [← hv]; unfold W; abel
  rw [hs,hw,norm_neg,norm_one,one_mul] at he
  exact he.trans (add_le_add (root_sup T _ Z e.target cap hc e.bound) e.cost)
end YM.Push.GridApprox
