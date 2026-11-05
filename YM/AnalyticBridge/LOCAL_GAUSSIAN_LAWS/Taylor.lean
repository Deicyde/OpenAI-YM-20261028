import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.CutGerm
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Step
import YM.Next.SCHEDULE.Postal

/-!
# Pricing the *sector* kernel with the no-hole inverse jets

E complaint 8641-8678. Work on B=0 EXP-log link Taylor tests of all
finite orders (including just at value, no-hole with common x fixed).
No translation symmetry assumed on T.up, Arch alignment sewn by the
proved Gram lemmas. Quantitative bundle on active incl ordered/sym
and discrepancy from IDEAL (treeInverse at B=0 when used with actual
horizon--prove in next files), Pours variant at order 0, and tag/aggregate
currency on the raw identity-completed ordered discrepancy. Ports to
ordered **left-Lie** derivatives are a separate effort, don't infer
there. Include segment on exponential size of errors. Transfer tag
differences only as `Affine.changed` (same parent-origin variant) and
for the same measurements, no claiming costs on sums over tags by their
probabilities. No incidence masks differentiated.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented Presented
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent Mark TestD Affine Window
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}
namespace Assembly
variable {ρ E ι v' X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {A B : E → Matrix ι ι ℝ} {p : ρ → E} {C : Mark ρ X} {D : Cost X} {a : ι → X} {k : ℕ} {η M N : ℝ}

lemma bundle_plus {o : E} (h : Bundle p C D a a A o k η M) (v : Bundle p C D a a B o k η N) :
    Bundle p C D a a (fun x => A x+B x) o k η (M+N) := by
  refine ⟨h.smooth.add v.smooth,fun l e => ?_⟩
  rw [TestD.jet_add p l (TestD.smooth_of_le h.smooth e) (TestD.smooth_of_le v.smooth e)]
  exact (h.bound _ e).add (v.bound _ e)



private def castMirror (ι : Type) [Fintype ι] : Matrix ι ι ℝ →L[ℝ] Matrix ι ι ℝ := LinearMap.toContinuousLinearMap {
  toFun := mirror
  map_add' := fun x y => by unfold mirror; rw [transpose_add,add_add_add_comm,smul_add]
  map_smul' := fun t x => by
    unfold mirror; rw [transpose_smul,← smul_add,smul_smul]; change _ = t • _; rw [smul_smul,mul_comm] }

lemma bundle_reflect {o : E} (h : Bundle p C D a a A o k η M) :
    Bundle p C D a a (fun x => mirror (A x)) o k η (M+M) := by
  let L := castMirror ι
  have he : (fun x => mirror (A x))=L ∘ A := rfl
  constructor
  · rw [he]; exact L.contDiff.contDiffAt.comp o h.smooth
  intro l e
  rw [he,Function.comp_def]; erw [TestD.jet_linear p l L (TestD.smooth_of_le h.smooth e)]
  let Q := jet p A l o
  have hh := (h.bound l e).add (h.bound l e).flip -- add combines, abs of half their sum
  apply hh.abs_le
  intro i j
  change |(1/2:ℝ) * _| ≤ |(Q+Q.transpose) i j|
  rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num)

section quote
variable (S : StepData c f) (T : Tube G S) (x : ℝ) (k : S.Choices) (U : Stores S) (F : Forest S.ratio) (g : Geometry)
    (hp : Larger (G:=G) S) {s J Λ : ℝ} (hT : T.up.Bounds T.high s J Λ) (hJ : 0 ≤ J)
include hp hT hJ

/-- The discrepancy is from the full ideal affine inverse germ
on the *same* tree and data, compared with ordinary spatial marks and
all real ∂_B orders ≤ k1. Explicit price splits up into exponential
window loss and path-cut loss with the *same* d,m as in FR. -/
theorem total (k1 : ℕ) (u : ℝ) (h : 0≤u) (hc : Clear S x U F) (hB : 120≤radiusB x) :
    let γ := footprint G S.patch S.kernel T.high k1 J s; let a := headGap G S.patch S.kernel T.high
    let V := load G S.patch S.kernel T.high k1 J s; let M := stageCost G S.patch S.kernel T.high k1 J s
    let C0 := meter k1 k1 M 1 (rise V a)*drain u
    let N := Real.exp (-(s/4)*(till x:ℕ))*(2*tagPrice 1 k1 (phasePrice G S.patch S.kernel k1 J s) (phasePrice G S.patch S.kernel k1 J s))
    let err := TestD.patchFee γ ((radiusB x/60:ℕ):ℝ) M 1 V C0 k1 + tagPrice 1 k1 (tagPrice 1 k1 C0 N) C0
    let e := opened G S x U F hc
    let Q (B : Coarse G c) := Rows.gram T x (enroll B) k (shots S x) U F
    let Ordered B := (pane (sectorW G S x U F g) (Q B) u).submatrix e e
    let Ideal B := resolve (Affine.primary S F k T.high T.up Affine.all B) u
    let P H (v : ℝ) := Bundle (ray G c) (marks G c γ) (native c) (theta _ F) (theta _ F) H 0 k1 γ v
    P (fun B => Ordered B-Ideal B) err ∧ P (fun B => mirror (Ordered B)-Ideal B) (2*err) := by
  intro γ a V M C0 N err e Q O I P
  have hw : Sheet T.up s J := hT.rows
  let Z := setSurvey (treeW G S x F g) (bars_hasCenters (tree_bars G S x F g hB))
  let P' := Affine.primary S F k T.high T.up (Affine.shorter (till x))
  have he := Affine.adjusting F k hT.width hJ hw hp T.high k1 (Affine.shorter (till x)) h Z (bars_near (tree_bars G S x F g hB))
  have hi := Affine.shortening F k hT.width hJ hw hp T.high k1 (till x) h
  let H := bundle_plus he hi
  have hb : (fun B => O B-I B) =ᶠ[𝓝 0] fun B => (Z.inspect (P' B) u - resolve (P' B) u) + (resolve (P' B) u-I B) := by
    filter_upwards [notarized S T x k U F hT hp.1 g] with B H
    rw [inspect_sets]
    have hv : O B=pane (treeW G S x F g) (P' B) u := ((H.2 hc).2 u)
    rw [hv]; abel
  have hO : P (fun B => O B-I B) err := H.glue hb.symm
  refine ⟨hO,(bundle_reflect hO).glue ?_ |>.mono le_rfl (le_of_eq (by ring))⟩
  refine Eventually.of_forall fun B => ?_
  have hh : (Affine.primary S F k T.high T.up Affine.all B).IsSymm := by
    unfold Affine.primary Affine.block
    apply Matrix.IsSymm.submatrix
    apply Matrix.IsSymm.smul
    -- sum
    unfold Matrix.IsSymm channel squareQ
    simp [Matrix.transpose_sum,Matrix.transpose_add,Matrix.transpose_smul,Matrix.transpose_mul]
  dsimp only
  rw [mirror_sub,mirror_symm_eq (show I B |>.IsSymm from symm_resolve _ hh _)]

omit hp hT hJ in
/-- In particular for E Sigma Sigma_0, u=0, OG fog proper.
Approximation in same P currency. -/
lemma covered_fog (hc : Clear S x U F) (B : Coarse G c) :
    let e := opened G S x U F hc
    let Q := Rows.gram T x (enroll B) k (shots S x) U F
    ((fog U F T x (enroll B) k).submatrix e e)=mirror ((pane (panels U F) Q 0).submatrix e e) := by
  intro e Q; rw [pane_zero]; rfl

omit hp hT hJ in
lemma covered_mid (hc : Clear S x U F) (B : Coarse G c) :
    let e := opened G S x U F hc
    let Q := Rows.gram T x (enroll B) k (shots S x) U F
    ((midFog U F T x (enroll B) k).submatrix e e)=mirror ((pane (sectorW G S x U F .midpoint) Q 0).submatrix e e) := rfl
end quote
end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
