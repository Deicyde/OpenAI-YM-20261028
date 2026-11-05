import YM.Next.BOUNDARY.Core
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion
import YM.SectorNext.VACUUM_NORMALIZATION.Etch



/-!
# Price the local logarithm term on the same licensed window

Ancillary factor call for , avoiding an extra future socket
for matrices using the fixed-L real sector prices.

This uses the previous VACUUM_NORMALIZATION panel technology for
spectral log diagonal values, not touching either ratioLog trace
expansion task.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.AnnulusRatioInsertions.FS
open Function Filter Lattice Wilson RG RG.Patch Precision Exterior Tree MeasureTheory Metric Matrix
open Next.SectorChange Next.SectorChange.Motion Next.SectorChange.Rows Next.SectorChange.Gaussian
open Pressure Pressure.Tube Pressure.Stores Bid Push.SectorMeasure Push.SectorMeasure.Oriented 
open Tier Wisps Schur LocalJet Completion SectorNext.Vacuum Panel Unitary

open scoped Topology InnerProductSpace BigOperators Classical ContDiff Matrix.Norms.Frobenius Push.SectorMeasure

section spectral
variable {ι : Type} [Fintype ι] [DecidableEq ι]
/-- Standard positive-spectrum matrix logarithm (only using this
on posdef matrices). Computational spectral definition from mathlib;
`Matrix.IsHermitian.cfc_eq` for link with continuous functional calculus if
needed. No theorem uses a value off the Hermitian case; extend there by zero.
-/
def nativeLog (A : Gaussian.Table ι) := if h : A.IsHermitian then h.cfc Real.log else 0

variable {A : Gaussian.Table ι} {η L : ℝ}


def perSlot (η L : ℝ) := Panel.mist η L 0 + |Real.log L|
lemma perSlot_pos (he : 0<η) (hL : η≤L) : 0 ≤ perSlot η L := by
  have ht : 0<1-Panel.steep η L := by unfold Panel.steep; rw [sub_sub_cancel]; exact div_pos he (he.trans_le hL)
  unfold perSlot Panel.mist; simp only [pow_zero,one_mul]; positivity





/-- Allow even W omitting its own root (will only use panels that include it),
and expose true extension by zero there. Principal positive matrix here is NOT
recomputed from rows truncated AGAIN to the window. -/
def ticket (A : Gaussian.Table ι) (X : ι→Set ι) (i : ι) : ℝ := if h : i∈X i then
    nativeLog (Schur.principal A (X i)) ⟨i,h⟩ ⟨i,h⟩ else 0

lemma fits (h : A.IsHermitian) (hx : Numeric A η L) (he : 0<η) (s : Set ι) :
    let Q := Schur.principal A s
    Q.IsHermitian ∧ Numeric Q η L ∧ Q.PosDef := by
  intro Q
  have ht : Gapped A η := fun i => sumSq_dot i |>.symm ▸ (hx i).1
  have hh : Gapped (-A) (-L) := by
    intro i; rw [Matrix.neg_mulVec,dotProduct_neg]; rw [sumSq_dot]; have h := (hx i).2; linarith
  have hH : Q.IsHermitian := h.submatrix _
  have hg := held_gap ht s
  have hv := held_gap hh s
  refine ⟨hH,fun i=>⟨?_,?_⟩,Schur.dissolves hg (Matrix.isHermitian_iff_isSymm.mp hH) he⟩
  · rw [← sumSq_dot]; exact hg i
  have h0 := hv i
  change _ ≤ _ ⬝ᵥ ((Schur.principal (-A) s) *ᵥ i) at h0
  rw [show Schur.principal (-A) s=-Q from rfl,Matrix.neg_mulVec,dotProduct_neg,sumSq_dot] at h0
  linarith


end spectral

section active
variable {G : Gauge} {c f : Side} {S : StepData c f}
variable (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (x : ℝ) (V : Config G c) (k : S.Choices)

/-- The cut affvd precision on all the genuine links with identity
completion from the Gaussian implementation. Use same permutation to read
local *color block* at a physical link index. -/
abbrev key := (Rows.In (G:=G) x A F ⊕ vacant A F x G)
def embossed : Gaussian.Table (key (G:=G) A F x) := Completion.wide (Rows.gram T x V k (shots S x) A F) 1

def sourced (i : Bond f) (j : G.ColorIndex) : key (G:=G) A F x := (sorted A F (G:=G)).symm (i,j)
def ember (i : Bond f) := ∑ j:G.ColorIndex, ticket (embossed T A F x V k) (allPanels A F) (sourced A F x i j)

/-- Cut same-family flat comparator. The Native kinetic matrix on
F.Free is this exactly through `native_equiv`. Use BEFORE even that
reindex if needing the prices here.
-/
def clean (S : StepData c f) : Stores S := ⟨∅,∅,∅⟩



def localPair (i : Bond f) := -(1/2)*(ember T A F x V k i - ember T (clean S) F x 1 k i)



def packageCost (η L : ℝ) := (Fintype.card G.ColorIndex:ℝ)*perSlot η L

section measures
variable {L η : ℝ} (he : 0<η) (hL : η≤L) (h : (embossed T A F x V k).IsHermitian) (hh : Numeric (embossed T A F x V k) η L)
  (h0 : (embossed T (clean S) F x 1 k).IsHermitian) (h1 : Numeric (embossed T (clean S) F x 1 k) η L)
include he hL h hh





include h0 h1







end measures
end active
end YM.AnalyticBridge.AnnulusRatioInsertions.FS
