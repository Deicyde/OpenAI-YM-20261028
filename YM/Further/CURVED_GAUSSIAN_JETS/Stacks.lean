import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import YM.Further.CURVED_GAUSSIAN_JETS.Colors
import YM.Further.CURVED_GAUSSIAN_JETS.Signed
import YM.Next.ROTATIONS.Nodes
import YM.Push.CUTOFF_PROJECTORS.Equations

/-!
# Concatenations for this real sector Gram (counting both directions)
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Further.CurvedGaussianJets.Stacks
open Matrix Function SectorNext.Vacuum Precision RG Lattice Progress.StationaryScenes
open scoped Matrix.Norms.Frobenius Topology BigOperators Classical
variable {I J X Y K : Type*} [Fintype I] [Fintype J] [Fintype X] [Fintype Y] [DecidableEq J] [DecidableEq I] [DecidableEq X]

def stack (A : Matrix X I ℝ) (B : Matrix Y I ℝ) : Matrix (X ⊕ Y) I ℝ := Matrix.of (Sum.elim A B)
def normalize (A : Signed → Matrix X I ℝ) : Matrix (Signed × X) I ℝ := Matrix.of fun i j => ((Real.sqrt (Fintype.card Signed))⁻¹ * A i.1 i.2 j)
def tall (A : Signed → Matrix X I ℝ) (B : Signed → Matrix Y I ℝ) (D : Matrix J I ℝ) := stack (normalize A) (stack (normalize B) D)
lemma stack_law (A : Matrix X I ℝ) (B : Matrix Y I ℝ) : gram (stack A B) = gram A + gram B := by ext; rw [gram,Matrix.mul_apply,Fintype.sum_sum_type]; rfl
lemma normalize_law (A : Signed → Matrix X I ℝ) : gram (normalize A) = Rot.average (fun s=> gram (A s)) := by
  ext i j; rw [gram, Matrix.mul_apply,Fintype.sum_prod_type, Rot.average, Matrix.of_apply,Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _=> ?_
  have ht : (Real.sqrt (Fintype.card Signed : ℝ))⁻¹ ^2 = ((Fintype.card Signed:ℝ))⁻¹ := by rw [inv_pow,Real.sq_sqrt (by positivity)]
  rw [gram,Matrix.mul_apply,Finset.mul_sum]; exact Finset.sum_congr rfl fun x _=> by simp only [transpose_apply,normalize,Matrix.of_apply,←ht]; ring
lemma average_add (A B : Signed → Table I) : Rot.average (fun i => A i+B i)=Rot.average A+Rot.average B := by ext; simp [Rot.average, Finset.sum_add_distrib]; ring
lemma tall_gram (A : Signed → Matrix X I ℝ) (B : Signed → Matrix Y I ℝ) (D : Matrix J I ℝ) :
    gram (tall A B D) = Rot.average (fun s => gram (A s)+gram (B s)) + gram D := by rw [tall,stack_law,stack_law,normalize_law,normalize_law,average_add,add_assoc]
lemma stack_energy (A : Matrix X I ℝ) (B : Matrix Y I ℝ) (x : Vec I) : (∑ i, ((stack A B *ᵥ x) i)^2) = ∑ i, ((A *ᵥ x) i)^2 + ∑ i, ((B *ᵥ x) i)^2 := by rw [Fintype.sum_sum_type]; rfl
lemma share_energy (A : Signed → Matrix X I ℝ) (x : Vec I) : (∑ i, ((normalize A *ᵥ x) i)^2) = (Fintype.card Signed : ℝ)⁻¹ * ∑ s,∑ i, ((A s *ᵥ x) i)^2 := by
  have ht : (Real.sqrt (Fintype.card Signed : ℝ))⁻¹ ^2 = ((Fintype.card Signed:ℝ))⁻¹ := by rw [inv_pow,Real.sq_sqrt (by positivity)]
  rw [Fintype.sum_prod_type]; unfold normalize Matrix.mulVec dotProduct; simp_rw [Matrix.of_apply, mul_assoc, ← Finset.mul_sum,mul_pow, ht,← Finset.mul_sum]


variable {n : Side} {loc : I → Site n} {w C C' D D' L L' : ℝ}
lemma gram_bill (hw : 0≤w) {a : Y → Site n} (M : Matrix Y I ℝ) (u v : ℝ) (hm : Green.Both a loc M w u v) (hu : 0 ≤ u) : Rows.Bill loc w (gram M) (v*u) := Rows.of_rows (A:=gram M) (Matrix.isHermitian_conjTranspose_mul_self M)
      (hm.2.multiply hw hm.1 hu)
lemma tall_bill {A : Signed → Matrix X I ℝ} {B : Signed → Matrix Y I ℝ} {E : Matrix J I ℝ}
    {a : Signed → X → Site n} {b : Signed → Y → Site n} {l : J → Site n}
    (h : ∀ s, Green.Both (a s) loc (A s) w C C') (hb : ∀ s, Green.Both (b s) loc (B s) w D D') (he : Green.Both l loc E w L L')
    (hw : 0≤w) (hC : 0≤C) (hD : 0≤D) (hL : 0≤L) : Rows.Bill loc w (gram (tall A B E)) (C'*C+D'*D+L'*L) := by
  rw [tall_gram]; exact Rows.plus (Rot.average_bill _ fun s=> Rows.plus (gram_bill hw _ _ _ (h s) hC) (gram_bill hw _ _ _ (hb s) hD)) (gram_bill hw E _ _ he hL)

lemma gram_scale (A : Matrix X I ℝ) (v : ℝ) : gram (v • A) = (v^2) • gram A := by rw [gram,gram,transpose_smul,Matrix.smul_mul,Matrix.mul_smul, smul_smul,pow_two]
lemma gram_cols (A : Matrix X I ℝ) (e : J → I) : gram (A.submatrix id e) = (gram A).submatrix e e := by rw [gram, gram, transpose_submatrix]; exact submatrix_mul_equiv _ _ e (Equiv.refl X) e
lemma same_cols (A : Matrix Y X ℝ) (B : Matrix X I ℝ) (e : J → I) : (A*B).submatrix id e = A * B.submatrix id e := (submatrix_mul_equiv _ _ id (Equiv.refl X) e).symm
lemma gram_row (K : Type*) [Fintype K] [DecidableEq K] (A : Matrix X I ℝ) : gram (Tint.row K A) = Tint.row K (gram A) := by rw [gram,gram, ← Tint.transpose,← Tint.product]
lemma row_avg (K : Type*) [Fintype K] [DecidableEq K] (A : Signed → Table I) : Rot.average (fun i=>Tint.row K (A i)) = Tint.row K (Rot.average A) := by
  ext i j; simp [Tint.row_apply,Rot.average]
lemma col_avg (A : Signed → Table I) (e : J → I) : Rot.average (fun i => (A i).submatrix e e) = (Rot.average A).submatrix e e := rfl
lemma row_weight (K : Type*) [DecidableEq K] (A : Table I) (v : ℝ) (e : J → I) :
    v • (Tint.row K (A.submatrix e e)) = Tint.row K ((v • A).submatrix e e) := by
  rw [submatrix_smul,Tint.row,Tint.row]; exact (smul_kronecker ..).symm
lemma row_plus (K : Type*) [DecidableEq K] (A B : Table I) (e : J → I) :
    Tint.row K ((A+B).submatrix e e) = Tint.row K (A.submatrix e e)+Tint.row K (B.submatrix e e) := Matrix.add_kronecker ..
end YM.Further.CurvedGaussianJets.Stacks
