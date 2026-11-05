import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.LinearAlgebra.Lagrange
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.AffineMatch
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Distinct
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Padded
import YM.Next.BOUNDARY.Coordinates
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Post
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.Push.FREE_RESOLVENT.AffineResolvent


/-!
# Active and raw matrices of the no-hole comparison

For eventual-equality and all-order jet use about \mathsf B=0.
Expose the algebraic coupons separately (if using with other actual
materials and valid `collective`). Handle singular submatrices in the
active equivalence; requirements for Pad are not all granted unless
hS supplied and nhds restriction observed or using the weighted
comparison. Include at the ACTUAL Stores with no chill, eg any whose
flags are empty and data specify a clear patch. Stencils still `shots`.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Push.SectorMeasure Oriented 
open Next SectorChange SectorChange.Rows SectorChange.Gaussian Wisps
open FreeResolvent
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f n : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}

namespace Assembly

/-- Reindex even the ordered survey. Need all centers in e.g.
shift directions? not for this pure lemma. -/
lemma pane_reindex {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (U : β→Set β) (Q : Gaussian.Table β) (u : ℝ) :
    (pane U Q u).submatrix e e=
      pane (fun i => e ⁻¹' U (e i)) (Q.submatrix e e) u := by
  ext i j
  by_cases he : e i∈U (e j)
  · by_cases hj : e j∈U (e j)
    · let W := U (e j); let T := e ⁻¹' W
      let E : T ≃ W := Equiv.ofBijective (fun x : T => (⟨_,x.2⟩ : W))
        ⟨fun x y h => Subtype.ext (e.injective (congr_arg Subtype.val h)),fun x => ⟨⟨e.symm x.val, show e (e.symm x.val)∈W from (by rw [e.apply_symm_apply]; exact x.2)⟩,Subtype.ext (e.apply_symm_apply _)⟩⟩
      let A := Schur.principal Q W
      rw [Matrix.submatrix_apply,pane_read U _ _ hj he,pane_read (fun i => e ⁻¹' U (e i)) (Q.submatrix e e) u (show j∈e ⁻¹' U (e j) from hj) he]
      change (A + u • 1)⁻¹ ⟨e i,he⟩ ⟨e j,hj⟩=(Schur.principal (Q.submatrix e e) (e ⁻¹' W)+u • 1)⁻¹ ⟨i,he⟩ ⟨j,hj⟩
      rw [show (Schur.principal (Q.submatrix e e) (e ⁻¹' W):Matrix T T ℝ)=A.submatrix E E from rfl,
        ← FreeResolvent.shift_compress E _ u E.injective,inverse_reindex]; rfl
    · change pane U Q u (e i) (e j) = _
      rw [pane_absent U _ _ (Or.inl hj),pane_absent (fun i => e ⁻¹' U (e i)) (Q.submatrix e e) u (show j ∉ e ⁻¹' U (e j) ∨ i ∉ e ⁻¹' U (e j) from Or.inl hj)]
  change pane U Q u (e i) (e j)=_
  rw [pane_absent U _ _ (Or.inr he),pane_absent (fun i => e ⁻¹' U (e i)) (Q.submatrix e e) u (show j ∉ e ⁻¹' U (e j) ∨ i ∉ e ⁻¹' U (e j) from Or.inr he)]



variable (S : StepData c f) (T : Tube G S) (x : ℝ) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    {σ C Λ : ℝ} (hT : T.up.Bounds T.high σ C Λ)

def Clear := ∀ i : F.Free, ¬chill A x F i
variable (G)
/-- Canonical no-hole reindex (condition on *these* stores). -/
def opened (h : Clear S x A F) : FreeResolvent.Active G F ≃ In (G:=G) x A F := {
  toFun i := (⟨i.1,h i.1⟩,i.2)
  invFun i := (i.1.val,i.2)
  left_inv _ := rfl
  right_inv _ := rfl }
lemma bare_is_Clear : Clear S x (bareStores S) F := notChilled S F x


inductive Geometry
  | endpoint | midpoint

def rel (g : Geometry) (B : ℕ) : Bond f → Bond f → Prop := match g with
  | .endpoint => endMeet S B
  | .midpoint => midMeet S B

def sectorW (g : Geometry) : In x A F (G:=G)→Set (In (G:=G) x A F) := match g with
  | .endpoint => panels A F
  | .midpoint => midSets S (radiusB x) A F x G
def treeW (g : Geometry) : FreeResolvent.Active G F → Set (FreeResolvent.Active G F) :=
  fun i => {j | rel S g (radiusB x) i.1.val j.1.val}


lemma tree_sector (g : Geometry) (h : Clear S x A F) (i : FreeResolvent.Active G F) :
    (opened G S x A F h) ⁻¹' sectorW G S x A F g (opened G S x A F h i)=treeW G S x F g i := by cases g <;> rfl

lemma tree_bars (g : Geometry) (H : 120 ≤ radiusB x) : Schur.Bars (treeW G S x F g) (theta S.ratio F) (radiusB x/60) := by
  intro i j he
  change rel S g _ _ _
  cases g
  · exact endContains S H he
  exact midContains S H he



variable {G}

include hT

/-- Track cut R=till x; exact flat-neighborhood comparison even
for nonzero V placements. No assertion that `x` here is issued. -/
theorem notarized (hp : S.patch.Branches S.kernel G) (g : Geometry) :
    ∀ᶠ B : Coarse G c in 𝓝 0,
      let Q := Affine.block S k T.high T.up (Affine.shorter (till x)) B
      let Y := Rows.gram T x (enroll B) k (shots S x) A F
      let e := register A F x G
      Y=Q.submatrix e e ∧
        ∀ h : Clear S x A F,
          let t := opened G S x A F h
          let Z := Affine.primary S F k T.high T.up (Affine.shorter (till x)) B
          Y.submatrix t t=Z ∧
          ∀ u, (pane (sectorW G S x A F g) Y u).submatrix t t=pane (treeW G S x F g) Z u := by
  filter_upwards [near_collective S hp (G:=G)] with B H
  intro Q Y e
  have he : Y=Q.submatrix e e := by
    unfold Y
    rw [sub_gram S T x B k A F hT hp, ← repaired_of_collective _ _ _ _ _ (H k)]
  refine ⟨he,?_⟩
  intro h t Z
  have hh : Y.submatrix t t=Z := by rw [he]; rfl
  exact ⟨hh,fun u => by rw [pane_reindex,hh,show (fun i => t ⁻¹' sectorW G S x A F g (t i))=treeW G S x F g from funext (tree_sector G S x A F g h)]⟩



omit hT in
/-- Need actual invertibility in the germ only for the pad inverse rule at
each u. One period, arbitrary I. Could also use configuring *Wearing*
back on actual unshifted prices at nonzero V rather than continuity if
these hold there. -/
lemma shells_near {α β Z : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [NormedAddCommGroup Z]
    (e : β ↪ α) (W : α→Set α) (T : β→Set β) (hW : aperture e W = T) (hc : ∀ i, i∈W i)
    (Q : Z→Matrix β β ℝ) (Y : Z→Matrix α α ℝ) (x : Z)
    (hQ : ContinuousAt Q x) (hh : (fun z => shells e (Q z) 1) =ᶠ[𝓝 x] Y)
    (η : ℝ) (hη : 0 < η) (hA : FreeResolvent.Gap (Q x) η) (u : ℝ) (hu : 0≤u) :
    (fun B => shells e (pane T (Q B) u) (1+u)⁻¹) =ᶠ[𝓝 x] fun B => (setSurvey W hc).inspect (Y B) u := by
  have hU (i : α) :=
    let a := ((↑): (e ⁻¹' W i) → β)
    TestD.germ_valid (A:=fun z => (Q z).submatrix a a) (x:=x) (u:=u) (((hA.submatrix a Subtype.val_injective).shift u).unit_det (add_pos_of_pos_of_nonneg hη hu)) ((continuous_id.matrix_submatrix a a).continuousAt.comp hQ)
  filter_upwards [eventually_all.mpr hU,hh] with z h hr
  rw [inspect_sets, ← hr,shells_pane _ _ _ _ (fun i => h i) (by positivity) hc,hW]

lemma ready (hp : Larger (G:=G) S) (ha : 0≤C) (h : Clear S x A F) :
    let Q B := Rows.gram T x (enroll B) k (shots S x) A F
    ContinuousAt Q 0 ∧ FreeResolvent.Gap (Q 0) (Affine.headGap G S.patch S.kernel T.high) := by
  let p := opened G S x A F h
  let J := Affine.primary S F k T.high T.up (Affine.shorter (till x))
  have he := Affine.knows F k hT.width ha (show Affine.Sheet T.up σ C from hT.rows) hp T.high 0 (Affine.shorter (till x))
  let a := Affine.headGap G S.patch S.kernel T.high
  have hx := notarized S T x k A F hT hp.1 .endpoint
  intro Q
  have hz : Q =ᶠ[𝓝 0] fun B => (J B).submatrix p.symm p.symm := by
    filter_upwards [hx] with B hx
    have hh : (Q B).submatrix p p=J B := (hx.2 h).1
    rw [← hh]; ext; simp
  constructor
  · apply ContinuousAt.congr_of_eventuallyEq ?_ hz
    exact (continuous_id.matrix_submatrix p.symm p.symm).continuousAt.comp he.smooth.continuousAt
  rw [show Q 0=(J 0).submatrix p.symm p.symm from hz.self_of_nhds]
  exact (Affine.directGap _ _ k T.high T.up _ hp).submatrix p.symm p.symm.injective


end Assembly
end YM.AnalyticBridge.LocalGaussianLaws
