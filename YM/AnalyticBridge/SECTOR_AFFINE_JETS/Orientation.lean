import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Postal
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
import YM.Push.FREE_RESOLVENT.JetWindows


/-!
# H-symmetry of the covariance prescription

Check rotated data too. Use the actual endpoints `panels`; for rotating
edge variables keep the varying adjoint columns. Important subtlety:
`shots`, conservative neighborhoods of *possible* affine inputs, test at
an INITIAL fine endpoint. Don't assume these balls (or which curb rows
selected) permute on reversing an edge. D itself, computed in active
columns, can use `selected_all`: value is zero already on any unselected
rows. Not claiming that all other constituents of the affidavit/cut measure
have individual tagwise symmetry.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.SectorAffine.Identity

open Filter Function Set Lattice Wilson RG Precision Pressure Tree Exterior
open YM.Next   
  
open   YM.ProjectorNext.Equivariance
open Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace Classical Matrix.Norms.Frobenius

variable {G : Gauge} {P : Patch} {c f n : Side} {S : StepData c f} {A : Stores S} {F : Forest S.ratio}
variable {k : S.Choices} {x : ℝ} {T : Tube G S} {V : Config G c}
section permutation

private lemma affine_zero (s : Signed) (x : Site c) : affine s 0 x = s.act x := add_zero _








private lemma moved_pos (s : Signed) (y : Site f) (i : Axis) (h : s.flip i=false) :
    s.act (y+step i)=s.act y+step (s.perm i) := by simpa only [affine_zero] using StepData.possite s 0 y i h
private lemma moved_neg (s : Signed) (y : Site f) (i : Axis) (h : s.flip i=true) :
    s.act (y+step i)=s.act y-step (s.perm i) := by simpa only [affine_zero] using StepData.negsite s 0 y i h
















end permutation

section change



lemma top_copy (s : Signed) (V : Config G c) :
    replica S.ratio (pull s 0 V)=pull s 0 (replica S.ratio V) := by
  let p := S.ratio.parent
  have h (i) := Ratio.parent_signed S.ratio S.patch.odd_side i s
  funext e
  rw [pull_formula]; rw [replica]; simp_rw [pull_formula,send_formula,affine_zero]; unfold replica
  let y := S.ratio.parent e.1
  let w := e.1+Lattice.step e.2; let j : Site f := Lattice.step (s.perm e.2)
  cases hh : s.flip e.2
  · have hp : S.ratio.parent (s.act e.1+Lattice.step (s.perm e.2))=s.act (S.ratio.parent w) := by
      rw [← moved_pos _ _ _ hh,h w]
    simp only [Bool.false_eq_true,↓reduceIte,h,hp,s.act_injective.eq_iff]
    rfl
  have hp : S.ratio.parent (s.act e.1-j) = s.act (S.ratio.parent w) := by
    rw [← moved_neg s e.1 e.2 hh,h w]
  by_cases hk : S.ratio.parent w = y
  · simp only [↓reduceIte]; unfold w y at hk; rw [if_pos hk,sub_add_cancel,h _,hp]; simp only [w,hk,if_true,inv_one]
  have he : S.ratio.parent w=y+step e.2 := by
    unfold w; rw [Ratio.parents_hop S.ratio S.patch.odd_side]; split
    · rfl
    next hx => exact (hk (by unfold w; rw [Ratio.parents_hop S.ratio S.patch.odd_side,if_neg hx])).elim
  have hne := s.act_injective.ne hk
  simp only [↓reduceIte]; rw [if_neg hk,sub_add_cancel,h _,hp,if_neg hne.symm]
  rw [he,moved_neg _ _ _ hh]




















end change

section comparison
variable {K : Teller G}




end comparison
end YM.AnalyticBridge.SectorAffine.Identity
