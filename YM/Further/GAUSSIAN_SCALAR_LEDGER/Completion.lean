import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian
import YM.SectorNext.VACUUM_NORMALIZATION.Factors


set_option warningAsError false

/-!
# Identity completion after omitting actual frozen & tree coordinates

The tree links never enter `Full`. They could be inserted with an identity
block the same way. Not a free-space covariance assertion. We must not
multiply the active Jacobian for frozen Haar integrals. Edge `H=univ`
is covered too.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar

open Matrix Function Precision SectorNext.Vacuum Lattice RG Wilson Tree
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {c f : Side} {g : Ratio c f} {F : Forest g} {G : Gauge}

abbrev Standing (H : Finset F.Free) := {j : F.Free // j ∉ H}
abbrev Bits (G : Gauge) (H : Finset F.Free) := Standing H × G.ColorIndex
abbrev Hold (G : Gauge) (H : Finset F.Free) := (↥H) × G.ColorIndex

def mergeBits (H : Finset F.Free) (G : Gauge) : Bits G H ⊕ Hold G H ≃ Key F G :=
  (Equiv.sumComm _ _).trans ((Equiv.sumProdDistrib (↥H) (Standing H) G.ColorIndex).symm.trans
    (Equiv.prodCongr (Equiv.sumCompl (· ∈ H)) (Equiv.refl _)))

variable (G) in
lemma merge_active (H : Finset F.Free) (i : Bits G H) : mergeBits H G (Sum.inl i) =
    (i.1.val,i.2) := rfl

variable (G) in
lemma merge_inactive (H : Finset F.Free) (i : Hold G H) : mergeBits H G (Sum.inr i) =
    (i.1.val,i.2) := rfl

lemma count_stand (H : Finset F.Free) : Fintype.card (Standing H)=nt F-H.card := by
  change Fintype.card {i : F.Free // i ∉ H} = _; rw [Fintype.card_subtype_compl]
  rw [Fintype.card_coe]; rfl

variable (G) in
lemma count_bits (H : Finset F.Free) :
    Fintype.card (Bits G H)=(nt F-H.card)*Module.finrank ℝ G.Color := by
  change Fintype.card (Standing H × G.ColorIndex) = _; rw [Fintype.card_prod, count_stand H]; simp [Gauge.Color]

def blankOut (H : Finset F.Free) (A : Wall (Key F G)) : Wall (Bits G H) :=
  let i (x : Bits G H) := mergeBits H G (Sum.inl x)
  A.submatrix i i

def meet (H : Finset F.Free) (A : Wall (Bits G H)) (B : Wall (Hold G H)) : Wall (Key F G) :=
  reindex (mergeBits H G) (mergeBits H G) (Matrix.fromBlocks A 0 0 B)

def filled (H : Finset F.Free) (A : Wall (Bits G H)) := meet H A 1

lemma sortBits (H : Finset F.Free) (A : Wall (Bits G H)) (B : Wall (Hold G H)) :
    (meet H A B).submatrix (mergeBits H G) (mergeBits H G) = Matrix.fromBlocks A 0 0 B := by
  ext i j
  simp [meet]

lemma blank_meets (H : Finset F.Free) (A : Wall (Bits G H)) (B : Wall (Hold G H)) :
    blankOut H (meet H A B) = A := by
  ext i j; exact congr_fun (congr_fun (sortBits H A B) (Sum.inl i)) (Sum.inl j)

lemma paid_filled (H : Finset F.Free) (A : Wall (Bits G H)) : det (filled H A) = A.det :=
  identity_price F (mergeBits H G) _ _ (sortBits H A 1)

lemma hermitian_filled (H : Finset F.Free) (A : Wall (Bits G H)) (h : A.IsHermitian) :
    (filled H A).IsHermitian := by
  apply Matrix.IsHermitian.submatrix _ (mergeBits H G).symm
  exact isHermitian_fromBlocks_iff.mpr ⟨h, conjTranspose_zero, conjTranspose_zero,isHermitian_one⟩



lemma blank_positive (H : Finset F.Free) (A : Wall (Key F G)) (h : A.PosDef) :
    (blankOut H A).PosDef := h.submatrix ((mergeBits H G).injective.comp Sum.inl_injective)

section extension







lemma numeric_positive {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Wall ι) (h : A.IsHermitian)
    (a b : ℝ) (hA : Numeric A a b) (ha : 0 < a) : A.PosDef :=
  h.posDef_iff_eigenvalues_pos.mpr fun i => ha.trans_le (Panel.bill_quad h hA i).1



end extension
end YM.Further.GaussianScalar
