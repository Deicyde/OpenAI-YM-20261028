import Mathlib.Analysis.Fourier.Convolution
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Margins
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Window
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Lifts
import YM.Next.SCHEDULE.Blocks
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.FREE_RESOLVENT.JetWindows


/-!
# Complete-block naturality

Actual Gaussian windows here always contain whole color slots at each
included link. The weight matrix may change basis independently at each
slot (including the V rotation on reversal). Order convention: `e : new
→ old`, `R : new → (oldColor → newColor)`. Prove exact naturality of
principal-pane lookup + sym based on THIS condition; no equivariance of
individual scalar entries inferred by type. Sets still not Fintype-
numbering assumptions. Use gatherings afterwards to get naturality of
measures and dyeds.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set MeasureTheory ProbabilityTheory Matrix WithLp Next SectorChange SectorChange.Gaussian
open scoped Topology ENNReal Classical BigOperators InnerProductSpace

namespace ColorBook
variable {a b c k : Type} [Fintype k] [DecidableEq k] [Fintype a] [Fintype b] [Fintype c]
  [DecidableEq a] [DecidableEq b] [DecidableEq c]
variable (e : b ≃ a) (R : b → SectorChange.Gaussian.Table k)

/-- Block linear map on arrays. Read the indexing e in this direction
for pullbacks (orthogonal input to the new channel). -/
def onPage : Matrix (b×k) (a×k) ℝ := Matrix.of fun x y => if y.1=e x.1 then R x.1 x.2 y.2 else 0

lemma onPage_vec (x : SectorChange.Gaussian.Vec (a×k)) (i : b) (j : k) :
    (onPage e R *ᵥ x) (i,j) = (R i *ᵥ (fun l => x (e i,l))) j := by
  classical
  unfold onPage mulVec dotProduct
  simp only [Matrix.of_apply,Fintype.sum_prod_type,ite_mul,zero_mul]
  rw [Finset.sum_eq_single (e i)] <;> simp_all

lemma onPage_turn : (onPage e R).transpose=onPage e.symm (fun i => (R (e.symm i)).transpose) := by
  ext ⟨i,j⟩ ⟨l,m⟩
  simp only [onPage,Matrix.of_apply,Matrix.transpose_apply]
  by_cases hi : i=e l
  · subst i; simp
  have hh : l≠e.symm i := fun he => hi (by rw [he,e.apply_symm_apply])
  simp [hi,hh]

lemma onPage_mul (f : c ≃ b) (U : c → SectorChange.Gaussian.Table k) :
    onPage f U * onPage e R = onPage (f.trans e) (fun i => U i*R (f i)) := by
  ext ⟨i,j⟩ ⟨l,m⟩
  simp only [onPage,Matrix.mul_apply,Matrix.of_apply,Fintype.sum_prod_type,ite_mul,zero_mul]
  by_cases h : l=e (f i)
  · subst l; rw [Finset.sum_eq_single (f i)] <;> simp_all
  simp only [Equiv.trans_apply]; rw [if_neg (show l≠_ from h)]; exact Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => by
    by_cases h0 : x=f i
    · subst x; simp [h]
    simp [h0]

lemma onPage_id : onPage (Equiv.refl a) (fun _=> (1: SectorChange.Gaussian.Table k))=1 := by
  ext ⟨i,j⟩ ⟨l,m⟩
  by_cases h : i=l
  · subst i; simp [onPage,Matrix.one_apply]
  simp [onPage,Matrix.one_apply,h,Ne.symm h]

/-- Use ordinary transpose, there is no density factor here. -/
def Oriented (R : b → SectorChange.Gaussian.Table k) : Prop :=
  ∀ i, (R i).transpose*(R i)=1
lemma Oriented.reverse (h : Oriented R) i : R i*(R i).transpose=1 := mul_eq_one_comm.mp (h i)


lemma onPage_right (h : Oriented R) : onPage e R*(onPage e R).transpose=1 := by
  rw [onPage_turn,onPage_mul]; simpa [h.reverse] using onPage_id (a:=b) (k:=k) -- need rw
lemma onPage_left (h : Oriented R) : (onPage e R).transpose*onPage e R=1 := by
  rw [onPage_turn,onPage_mul]; unfold Oriented at h; simpa [h] using onPage_id (a:=a) (k:=k)

/-- Skimming commuting with locations, expands complete color matching
but no other site contributes. -/
lemma skim_read (M : SectorChange.Gaussian.Table (a×k)) (i l : b) (j m : k) :
    Density.skim (onPage e R) M (i,j) (l,m)=∑ x : k, (∑ y : k, R i j y * M (e i,y) (e l,x)) * R l m x := by
  -- collapse both sums on the sites
  have h (t : a × k) : (onPage e R * M) (i,j) t=∑ y : k, R i j y * M (e i,y) t :=
    onPage_vec e R (M.col t) i j
  unfold Density.skim; rw [Matrix.mul_apply,Fintype.sum_prod_type,Finset.sum_eq_single (e l)]
  · refine Finset.sum_congr rfl fun x _ => ?_; rw [h]; simp [onPage]
  · intro t _ he; simp [onPage,he]
  simp

lemma skim_times (h : Oriented R) (A B : SectorChange.Gaussian.Table (a×k)) :
    Density.skim (onPage e R) (A*B) = Density.skim (onPage e R) A * Density.skim (onPage e R) B := by
  let L:=onPage e R
  have he : L.transpose*L=1 := onPage_left e R h
  unfold Density.skim; change L*(A*B)*_ = L*A*L.transpose*(L*B*_)
  simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc L.transpose L, he, Matrix.one_mul]

lemma skim_shift (h : Oriented R) (A : SectorChange.Gaussian.Table (a×k)) (u : ℝ) :
    Density.skim (onPage e R) (A+u • 1) = Density.skim (onPage e R) A+u • 1 := by
  unfold Density.skim; rw [Matrix.mul_add,Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul,Matrix.mul_one,onPage_right _ _ h]

private def eqColour : (b × k) ≃ (a × k) := Equiv.prodCongr e (Equiv.refl k)

lemma skim_det (h : Oriented R) (M : SectorChange.Gaussian.Table (a×k)) :
    det (Density.skim (onPage e R) M)=M.det := by
  let q : a × k ≃ b × k := (eqColour e).symm
  let L := onPage e R; let X := L.submatrix q id
  have hh (N : SectorChange.Gaussian.Table (b×k)) : det (N.submatrix q q)=det N := Matrix.det_submatrix_equiv_self q N
  have ha : X*X.transpose=1 := by
    unfold X; rw [transpose_submatrix]; erw [Matrix.submatrix_mul_equiv L L.transpose q (Equiv.refl _) q]; unfold L; rw [onPage_right _ _ h,Matrix.submatrix_one_equiv]
  have hx := congr_arg Matrix.det ha
  rw [Matrix.det_mul,Matrix.det_transpose,Matrix.det_one] at hx
  rw [← hh]
  change det ((L*M*L.transpose).submatrix q q)=M.det
  rw [← Matrix.submatrix_mul_equiv _ L.transpose q (Equiv.refl _) q, ← Matrix.submatrix_mul_equiv L _ q (Equiv.refl _) (Equiv.refl _)]
  change det (X*M*(X.transpose)) = _
  rw [Matrix.det_mul,Matrix.det_mul, Matrix.det_transpose]
  calc
    _=det X * det X * det M := by ring
    _=_ := by rw [hx,one_mul]

lemma skim_inv (h : Oriented R) (M : SectorChange.Gaussian.Table (a×k)) :
    (Density.skim (onPage e R) M)⁻¹=Density.skim (onPage e R) M⁻¹ := by
  by_cases ht : IsUnit M.det
  · apply Matrix.inv_eq_right_inv; rw [← skim_times _ _ h,M.mul_nonsing_inv ht]
    unfold Density.skim; rw [Matrix.mul_one, onPage_right _ _ h]
  rw [Matrix.nonsing_inv_apply_not_isUnit _ ht,Matrix.nonsing_inv_apply_not_isUnit _ (show ¬IsUnit _ from (by rwa [skim_det e R h])),Density.skim]; simp

def sheet (W : a → Set a) (x : a × k) := {j : a × k | j.1 ∈ W x.1}
def skimWindow (W : a → Set a) (x : b) := e ⁻¹' W (e x)

def spread (W : a → Set a) (x : a × k) : (W x.1 × k) ≃ ↥(sheet W x) where
  toFun t := ⟨(t.1,t.2),t.1.2⟩
  invFun i := (⟨i.val.1,i.2⟩,i.val.2)
  left_inv _ := rfl
  right_inv i := by obtain ⟨⟨i,j⟩,_⟩ := i; rfl

def seat (s : Set a) : ↥(e ⁻¹' s) ≃ s := Equiv.ofBijective
  (fun x : e ⁻¹' s => (⟨_,x.2⟩ : s))
  ⟨fun _ _ H => Subtype.ext (e.injective (congr_arg Subtype.val H)),fun x => ⟨⟨e.symm x.val, show e (e.symm x.val)∈s from (by rw [e.apply_symm_apply]; exact x.2)⟩,Subtype.ext (e.apply_symm_apply _)⟩⟩

def tap (W : a → Set a) (x : a) (z : W x × k) : a × k := (z.1.val,z.2)

/-- Read in block form rather than subtype of product blocks. -/
lemma pane_color (W : a→Set a) (M : SectorChange.Gaussian.Table (a×k)) (u : ℝ) (i j : a) (v w : k)
    (h : i∈W j) (h' : j∈W j) :
    let X := (M+u • 1).submatrix (tap W j) (tap W j)
    pane (sheet W) M u (i,v) (j,w) = X⁻¹ (⟨i,h⟩,v) (⟨j,h'⟩,w) := by
  let a := spread W (j,w)
  rw [pane,SectorChange.Schur.per_read (sheet W) _ (show (j,w)∈sheet W (j,w) from h') (show (i,v)∈sheet W (j,w) from h)]
  let B:=Schur.principal (M+u • 1) (sheet W (j,w))
  intro X
  have he : B.submatrix a a=X := rfl
  rw [← he, inverse_reindex]; rfl

/-- Exact compatibility of ordered columns, under *whole* block windows,
all u. Even singular remains singular under these rules. Does **not**
require symmetry of Q. -/
theorem natural (W : a → Set a) (A : SectorChange.Gaussian.Table (a×k)) (u : ℝ) (H : Oriented R) :
    let L := onPage e R
    pane (sheet (skimWindow e W)) (Density.skim L A) u=Density.skim L (pane (sheet W) A u) := by
  intro L
  ext ⟨i,j⟩ ⟨l,m⟩
  unfold L
  rw [skim_read]
  let z := skimWindow e W
  let B := W (e l)
  by_cases h : e i ∈ B ∧ e l ∈ B
  · let M := (A+u • 1).submatrix (tap W (e l)) (tap W (e l))
    let T : z l → SectorChange.Gaussian.Table k := fun v => R v
    have ht : Oriented T := fun i => H i
    let v : z l ≃ B := seat e B
    have hx : i∈z l := h.1; have hv : l∈z l := h.2
    have hh : (Density.skim (onPage e R) A + u • 1).submatrix (tap z l) (tap z l)=Density.skim (onPage v T) M := by
      rw [← skim_shift e R H]
      ext ⟨a,b⟩ ⟨c,d⟩
      change Density.skim (onPage e R) (A+u • 1) (a.val,b) (c.val,d) = Density.skim (onPage v T) M (a,b) (c,d)
      rw [skim_read,skim_read]; rfl
    rw [pane_color z _ u i l j m hx hv, hh,skim_inv v T ht,skim_read]
    apply Finset.sum_congr rfl; intro q _
    change (∑ y, R i j y*_)*R l m q = _
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pane_color W A u (e i) (e l) r q h.1 h.2]; rfl
  have H' (j m : k) : pane (sheet z) _ u (i,j) (l,m)=0 := pane_absent (sheet z) (Density.skim L A) u ((not_and_or.mp h).elim (fun a => Or.inr a) Or.inl : (l,m) ∉ sheet z (l,m) ∨ (i,j) ∉ sheet z (l,m))
  have h' (j m : k) : pane (sheet W) A u (e i,j) (e l,m)=0 := pane_absent (sheet W) _ _ ((not_and_or.mp h).elim (fun a => Or.inr a) Or.inl : (e l,m) ∉ sheet W (e l,m) ∨ (e i,j) ∉ sheet W (e l,m))
  change pane (sheet z) (Density.skim L A) u (i,j) (l,m)=_
  simp_rw [H',h',mul_zero,Finset.sum_const_zero,zero_mul,Finset.sum_const_zero]



end ColorBook
end YM.AnalyticBridge.LocalGaussianLaws
