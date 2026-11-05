import YM.Push.SECTOR_MEASURE.Output
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen

/-!
# Fiber maps on the covariance coordinates

Apply blocks in real physical color bases. In particular no statement that
the varying orientation maps can be differentiated as constant frames.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine
open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next.Fluctuations YM.Next.SectorChange
open YM.Next.SectorChange.Rows YM.Next.SectorChange.Wisps YM.Next.SectorChange.Schur
open Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

structure LinkBasis (G : Gauge) (ι κ : Type) where
  loc : κ ≃ ι
  spin : κ → G.Color ≃L[ℝ] G.Color
  unit_norm (i : κ) (a : G.Color) : ‖spin i a‖=‖a‖

namespace LinkBasis
variable {G : Gauge} {ι κ : Type}

def changed (F : LinkBasis G ι κ) : LogArray G ι ≃ₗ[ℝ] LogArray G κ where
  toFun v i := F.spin i (v (F.loc i))
  map_add' a b := funext fun i => (F.spin i).map_add ..
  map_smul' v a := funext fun i => (F.spin i).map_smul ..
  invFun w i := (F.spin (F.loc.symm i)).symm (w (F.loc.symm i))
  left_inv a := funext fun i => by simp only [F.loc.apply_symm_apply,(F.spin _).symm_apply_apply]
  right_inv a := funext fun i => by simp only [F.loc.symm_apply_apply,(F.spin _).apply_symm_apply]



variable [Fintype ι] [Fintype κ]

def lifted (F : LinkBasis G ι κ) := colors.trans (F.changed.trans (colors (G:=G) (ι:=κ)).symm)



variable [DecidableEq ι] [DecidableEq κ]




def portal (F : LinkBasis G ι κ) : Matrix (κ×G.ColorIndex) (ι×G.ColorIndex) ℝ :=
  LinearMap.toMatrix' F.lifted.toLinearMap

omit [Fintype κ] [DecidableEq κ] in
lemma portal_eval (F : LinkBasis G ι κ) (v : Prices G ι) : F.portal *ᵥ v=F.lifted v := by
  unfold portal; rw [LinearMap.toMatrix'_mulVec]; rfl



end LinkBasis

section transport
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
variable {A D : Stores S} {F H : Forest S.ratio} {x : ℝ} {k t : S.Choices} {V W : Config G c}

/-- State symmetry in native matrices, keeping the *transfer* of the bases
explicit. At rotations the two active sets can differ. Doesn't assert the
entrywise *stencils* for auxiliary applications of the affine F0/selectors
are equivariant. -/
structure Intertwines (T : Tube G S) (x : ℝ) (A D : Stores S) (F H : Forest S.ratio) (k t : S.Choices)
    (V W : Config G c) (J : LinkBasis G (Active A x F) (Active D x H)) (L : LinkBasis G (Slots S) (Slots S)) : Prop where
  window (i j : In x D H (G:=G)) :
    i∈panels D H j ↔ meeting S x (J.loc j.1).val.val (J.loc i.1).val.val
  paths (a : LogArray G (Active A x F)) :
    bump T x W t (fresh x (shots S x) D H (J.changed a))=L.changed (bump T x V k (fresh x (shots S x) A F a))






end transport
end YM.AnalyticBridge.SectorAffine
