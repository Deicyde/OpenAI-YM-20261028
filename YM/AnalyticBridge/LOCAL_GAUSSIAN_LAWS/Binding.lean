import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ColourBooks
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.DensityPrice
import YM.Push.CUTOFF_PROJECTORS.Signed


/-!
# Orthogonal movement data consume the SAME field check

In real counting metric, including determinants, b (holds per y, possibly
shifted as prescribed), right-trivialized variations (a component map
between config fields). No choice of Gram root or ell-atom from pricing
needed. No hypothesis here of identical A; require ACTUAL diagrams on D
and F0 modulo only `D^T` for the b comparison (not full F0 if difference
lies only on zero-D rows, for `shots`). Does not infer all of dyed
covaries then (would additionally need full movement including suppressors,
row residual, sleeves & prescribed μ/branches). This is symmetry of the
window *Gaussian*. Include a version of the downstream law even with
$δ$ as impulse.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open ColorBook
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

section diff
variable {E H F N : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
  [NormedAddCommGroup F] [NormedAddCommGroup N] [NormedSpace ℝ E] [NormedSpace ℝ H]
  [NormedSpace ℝ F] [NormedSpace ℝ N]
/-- Include nonsmooth-germ case, on purpose (fderiv default).
Doesn't certify the number as an actual differential then. -/
lemma marks (e : E ≃L[ℝ] H) (f : F ≃L[ℝ] N) (A : E → F) (B : H → N) (h : B ∘ e = f ∘ A) (a : E) :
    fderiv ℝ B 0 (e a)=f (fderiv ℝ A 0 a) := by
  have he := congr_arg (fun p => fderiv ℝ p 0 a) h
  rw [e.comp_right_fderiv, f.comp_fderiv,map_zero] at he; exact he
end diff
namespace ColorBook
variable {G : Gauge} {a b c d : Type} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] (e : b ≃ a)

/-- Data on colors, not prescribing a coordinate matrix away from its
true norm. -/
def adBody (v : G.El) : G.Color ≃ₗᵢ[ℝ] G.Color := {
  G.adjoint v with
  invFun := G.adjoint v⁻¹
  left_inv x := by change G.adjoint v⁻¹ (G.adjoint v x)=_; rw [← G.adjoint_mul,inv_mul_cancel,G.adjoint_one]
  right_inv x := by change G.adjoint v (G.adjoint v⁻¹ x)=_; rw [← G.adjoint_mul,mul_inv_cancel,G.adjoint_one]
  norm_map' := G.norm_adjoint v }

variable {k : Type} [Fintype k] [DecidableEq k]
variable (R : b → EuclideanSpace ℝ k ≃ₗᵢ[ℝ] EuclideanSpace ℝ k)

def tagColor (i : b) : Matrix k k ℝ := LinearMap.toMatrix'
    ((WithLp.linearEquiv 2 ℝ _).toLinearMap.comp ((R i).toLinearEquiv.toLinearMap.comp ((WithLp.linearEquiv 2 ℝ _).symm.toLinearMap)))
lemma tag_runs (x : EuclideanSpace ℝ k) (i : b) : tagColor R i *ᵥ x.ofLp = ((R i) x).ofLp := LinearMap.toMatrix'_mulVec ..

lemma tag_checked : ColorBook.Oriented (tagColor R) := by
  intro i
  let L := tagColor R i
  have he (x y : k → ℝ) : ((L.transpose * L) *ᵥ y) ⬝ᵥ x=y ⬝ᵥ x := by
    rw [← Matrix.mulVec_mulVec,dotProduct_comm _ x,Matrix.dotProduct_transpose_mulVec,tag_runs R (WithLp.toLp 2 y), tag_runs R (WithLp.toLp 2 x)] 
    have hx (x y : EuclideanSpace ℝ k) : x.ofLp ⬝ᵥ y.ofLp=inner ℝ y x := by rw [PiLp.inner_apply]; rfl
    exact (hx _ _).trans (((R i).inner_map_map _ _).trans (hx (WithLp.toLp 2 y) (WithLp.toLp 2 x)).symm) 
  ext j k
  have h := he (Pi.single j 1) (Pi.single k 1)
  simpa only [mulVec_single_one,dotProduct_single,mul_one,col_apply,Pi.single_apply,one_apply,eq_comm] using h

/-- Direct sum equivalence on true color arrays, including unrelated
basis choices i.e. if pricing under a varying slice basis. -/
def readers : (a → EuclideanSpace ℝ k) ≃L[ℝ] (b → EuclideanSpace ℝ k) := LinearEquiv.toContinuousLinearEquiv {
  toFun x i := R i (x (e i))
  map_add' x y := by funext; simp
  map_smul' t x := by funext; simp
  invFun y i := (R (e.symm i)).symm (y (e.symm i))
  left_inv x := by funext; simp
  right_inv y := by funext; simp }

lemma onPage_read (R : b → G.Color ≃ₗᵢ[ℝ] G.Color) (x : LogArray G a) : onPage e (tagColor R) *ᵥ (tape.symm x)=
    tape.symm (readers (k:=G.ColorIndex) e R x) := by
  funext i; rcases i with ⟨i,j⟩; rw [onPage_vec]; exact congr_fun (tag_runs R (x (e i)) i) j

section grams
variable (F : d ≃ c) (T : d → EuclideanSpace ℝ k ≃ₗᵢ[ℝ] EuclideanSpace ℝ k)
variable (D : Matrix (c×k) (a×k) ℝ) (D' : Matrix (d×k) (b×k) ℝ)

/-- Inputs for consuming into covariance/b -- suffice reader
laws; not pretending different F.In etc defeq. Don't prescribe
that *all F0 rows* transform because an extra selected F0 at a
row with zero D (e.g. due to nonsymmetric potential stencil convention)
contributes zero b, although it affects residual etc. -/
theorem weaves (s' : d × k → ℝ) (q : c × k→ℝ)
    (h : ∀ v, D' *ᵥ (onPage e (tagColor R) *ᵥ v) = onPage F (tagColor T) *ᵥ (D *ᵥ v))
    (he : D'.transpose *ᵥ s'=D'.transpose *ᵥ (onPage F (tagColor T) *ᵥ q)) :
    let X := onPage e (tagColor R)
    D'.transpose*D'=Density.skim X (D.transpose*D) ∧ D'.transpose *ᵥ s'=X *ᵥ (D.transpose *ᵥ q) := by
  intro X; let W := onPage F (tagColor T)
  have hx : D'*X = W*D := by
    ext i j; have he := congr_fun (h (Pi.single j 1)) i
    have he' := he
    simp only [Matrix.mulVec_single_one] at he'
    exact he'
  have hi : X * X.transpose = 1 := onPage_right e _ (tag_checked R)
  have ht : W.transpose * W=1 := onPage_left F _ (tag_checked T)
  have h' : D'=W*D*X.transpose := by rw [← hx, Matrix.mul_assoc,hi,Matrix.mul_one]
  rw [he,h']; simp only [Matrix.transpose_mul,Matrix.transpose_transpose, Matrix.mulVec_mulVec,Density.skim,Matrix.mul_assoc]
  rw [← Matrix.mul_assoc W.transpose,ht,Matrix.one_mul]
  simp
end grams

/-- b and precision (or Gram) diagram then license naturality of
ANY ordered covariance here + mean. -/
theorem moves (Q : SectorChange.Gaussian.Table (a×k)) (Q' : SectorChange.Gaussian.Table (b×k))
    (s : SectorChange.Gaussian.Vec (a×k)) (s' : SectorChange.Gaussian.Vec (b×k)) (W : a → Set a)
    (Y : b → Set b) (u : ℝ) (hy : Y=skimWindow e W) (h : Q'=Density.skim (onPage e (tagColor R)) Q)
    (he : s'=onPage e (tagColor R) *ᵥ s) :
    let X := onPage e (tagColor R)
    let A := pane (sheet W) Q u; let B:=pane (sheet Y) Q' u
    B=Density.skim X A ∧ mirror B=Density.skim X (mirror A) ∧ offCenter B s'=X *ᵥ (offCenter A s) ∧ (mirror B).det=(mirror A).det := by
  intro X A B
  have ht := tag_checked R
  have hx : X.transpose*X=1 := onPage_left e _ ht
  have hB : B=Density.skim X A := by unfold B; rw [hy,h,natural e (tagColor R) _ _ _ ht]
  have ha : mirror B=Density.skim X (mirror A) := by
    rw [hB]; unfold Density.skim mirror; simp only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.mul_add,
      Matrix.add_mul,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,smul_add]
  refine ⟨hB,ha,?_,?_⟩
  · unfold offCenter; rw [he,hB, Density.skim, Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_mul]
    change - (X*(A.transpose*X.transpose)) *ᵥ (X*ᵥs)= _
    simp only [Matrix.mulVec_mulVec, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc, hx, Matrix.mul_one]
  rw [ha,skim_det e _ ht]
end ColorBook
end YM.AnalyticBridge.LocalGaussianLaws
