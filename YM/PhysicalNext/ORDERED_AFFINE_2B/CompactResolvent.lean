import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Epoch
import YM.PhysicalNext.ORDERED_AFFINE_2B.Journeys


/-!
# A compact analytic trick for the real u≥0 price entries

Aim: genuine ContDiffAt of each  chain price & each paired Lap
purchase that is used/multiplied later. NOT intersecting neighborhoods
with changing tags, nor promoting them from ContDiff to AnalyticAt on
all V or keeping complex radii. For integrated entries rewrite with

    r=1/(1+u) and B = 1+r(M-1)

on each *local* compressed W. Z=B⁻¹ gets nondegenerate throughout
r∈[0,1] incl at ∞. The quantities here extend off M arbitrarily as
smooth functions using a smooth determinant collar. Used for regularity
only: not re-implementing any definition with such a collar or taking
estimates on its boundary. Prices will still differentiate the actual
functions with true Handles.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.OrderedAffine2B.Compact
open Function Filter Set Lattice RG Wilson Precision
open Further Further.CurvedGaussianJets Matrix MeasureTheory
open scoped Topology BigOperators Classical ContDiff

section handle



end handle

variable {I K : Type} [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]
-- easier ambient derivative space
abbrev Input (I : Type) := I→I→ℝ

def bar (M : CurvedGaussianJets.Table K) (r : ℝ) := 1 + r • (M-1)
omit [Fintype K] in
lemma bar_pos (M : CurvedGaussianJets.Table K) (h : M.PosDef) {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : (bar M r).PosDef := by
  rcases eq_or_lt_of_le hr.1 with ht|ht
  · rw [bar,←ht,zero_smul,add_zero]; exact Matrix.PosDef.one
  have hs : bar M r = r • M + (1-r) • (1:CurvedGaussianJets.Table K) := by unfold bar; rw [smul_sub,sub_smul,one_smul]; abel
  rw [hs]; exact (h.smul ht).add_posSemidef (Matrix.PosSemidef.one.smul (sub_nonneg.mpr hr.2))

omit [Fintype K] in
lemma bar_shift {u r : ℝ} (h : (1+u)*r=1) (M : CurvedGaussianJets.Table K) : r • CurvedGaussianJets.shifted M u=bar M r := by
  have he : r*u=1-r := by linarith only [h]
  rw [CurvedGaussianJets.shifted,smul_add,smul_smul,he,bar,smul_sub,sub_smul,one_smul]; abel

lemma bar_linear (M : CurvedGaussianJets.Table K) (r : ℝ) (h : IsUnit (bar M r).det) :
   (bar M r)⁻¹ + r • ((M-1) * (bar M r)⁻¹)=1 := by
  rw [← Matrix.smul_mul]; conv_lhs => lhs; rw [← Matrix.one_mul (bar M r)⁻¹]
  rw [← Matrix.add_mul]; exact Matrix.mul_nonsing_inv _ h

omit [DecidableEq I] in
lemma det_smooth (X : Input I×ℝ→CurvedGaussianJets.Table K) (h : ∀ i j, ContDiff ℝ ∞ (fun p=> X p i j)) : ContDiff ℝ ∞ (fun p=> (X p).det) := by
  simp only [Matrix.det_apply,Units.smul_def,zsmul_eq_mul]; apply ContDiff.sum; intro s _; exact contDiff_const.mul (contDiff_prod (fun i _=> h _ _))
omit [DecidableEq I] in
lemma adj_smooth (X : Input I×ℝ→CurvedGaussianJets.Table K) (h : ∀ i j, ContDiff ℝ ∞ (fun p=> X p i j)) (i j : K) :
    ContDiff ℝ ∞ (fun p=> (X p).adjugate i j) := by
  simp only [Matrix.adjugate_apply]; refine det_smooth _ (fun k l=>?_); simp only [Matrix.updateRow_apply]; split; exact contDiff_const; exact h _ _

variable (W : CurvedGaussianJets.Windows I)
-- W is *fixed*, including bond locations in I. No derivative across
-- changing flag sets. These Z declarations specific to window cylinders.

def square (i : I) (p : Input I × ℝ) := bar (W.localGram (Matrix.of p.1) i) p.2


structure Pad where
  matrix (i : I) : Input I × ℝ → CurvedGaussianJets.Table ↥(W.box i)
  smooth (i : I) (j k : ↥(W.box i)) : ContDiff ℝ ∞ (fun p=> matrix i p j k)

variable {W}



namespace Pad
variable (p : Pad W)
def Y (a : Input I × ℝ) := Matrix.of fun (i j : I) => if hi : i∈W.box j then p.matrix j a ⟨i,hi⟩ (W.center j) else (0:ℝ)
def H (a : Input I × ℝ) := Matrix.of fun (i j : I) => if hi : i∈W.box j then ((W.localGram (Matrix.of a.1) j-1) * p.matrix j a) ⟨i,hi⟩ (W.center j) else 0





variable {r u : ℝ} (M : Input I) (h : (1+u)*r=1)
    (H₀ : ∀ i, let B:= square W i (M,r); 0<B.det ∧ p.matrix i (M,r)=B⁻¹)
include H₀
lemma cash : Y p (M,r) + r • H p (M,r) = 1 := by
  ext i j; unfold Y H; simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.of_apply]; split
  next hi =>
    let k : W.box j := ⟨i,hi⟩
    have hz := (H₀ j).2; rw [hz]; have ha := bar_linear (W.localGram (Matrix.of M) j) r (isUnit_iff_ne_zero.mpr (H₀ j).1.ne')
    have hQ : (1 : CurvedGaussianJets.Table (W.box j)) k (W.center j) = (1 : CurvedGaussianJets.Table I) i j := by simp [Matrix.one_apply,k,Windows.center,Subtype.ext_iff]
    exact (congr_fun (congr_fun ha k) _).trans hQ
  next hi => rw [Matrix.one_apply_ne (show i ≠ j from fun hh=> hi (by rw [hh]; exact W.within _))]; ring
include h


end Pad
end YM.PhysicalNext.OrderedAffine2B.Compact
