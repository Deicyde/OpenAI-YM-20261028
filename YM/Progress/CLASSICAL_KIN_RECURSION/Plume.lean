import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Group.Tannery
import YM.Analysis.Polydisc
import YM.Pressure.Seeds
import YM.Work.G05.Taylor


set_option warningAsError false

/-!
# Homogeneous comparison inside germs, with all factorials in the
stationary value and multileg tensor matching. No high-order analyticity on
the toroidal coefficients needed here, only ContDiffAt.
-/
set_option autoImplicit false
noncomputable section
open Filter Function
namespace YM.Progress.ClassicalKin
open Lattice RG Laurent Exterior Wilson Precision Tree
open YM.Tensor
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {k : ℕ}

/-- all lower jets, strictly -/
def Dormant (h : X→Y) (k : ℕ) := ∀ j,j<k → iteratedFDeriv ℝ j h 0=0

open Work.G05 in
lemma rightLog (h : X→Y) (v : Z →L[ℝ] X) (hh : ContDiffAt ℝ k h 0) :
    iteratedFDeriv ℝ k (h ∘ v) 0 = (iteratedFDeriv ℝ k h 0).compContinuousLinearMap (fun _=> v) := by
  let U:=blockTaylor k h
  have he : ContDiff ℝ k U:=blockTaylor_contDiff k h _
  have hu : ContDiffAt ℝ k h (v 0):=map_zero v |>.symm ▸ hh
  have ht : ∀ j≤k, iteratedFDeriv ℝ j U (v 0)=iteratedFDeriv ℝ j h (v 0) := by rw [map_zero]; exact blockTaylor_jets hh
  have hr := jets_comp v.contDiff.contDiffAt v.contDiff.contDiffAt he.contDiffAt hu rfl (fun _ _=>rfl) ht k le_rfl
  rw [← hr,v.iteratedFDeriv_comp_right he 0 le_rfl,ht k le_rfl,map_zero]

/-- length-n partitions will only use the first-order slots -/
private lemma atomDegree (c : OrderedFinpartition k) (h : c.length=k) (i) : c.partSize i=1 := by
  have he : (∑ i,c.partSize i)=k := by
    simpa only [Fintype.card_fin,Fintype.card_sigma] using Fintype.card_congr c.equivSigma
  have hi := c.partSize_pos i
  by_contra! hx
  have ht (j) := c.partSize_pos j; have hg : (1:ℕ) < c.partSize i := by omega
  have hv : ∑ _ : Fin c.length, (1:ℕ) < ∑ i,c.partSize i := Finset.sum_lt_sum (fun a _ => ht a) ⟨i,Finset.mem_univ _, hg⟩
  simp [he,h] at hv

/-- leading composition under analytic symmetry with all earlier coefficients
agreed. Do not assert this when comparing just a lone matched coefficient!
-/
lemma wakes (h : Y→Z) (f : X→Y) (hh : ContDiffAt ℝ k h 0) (hf : ContDiffAt ℝ k f 0)
    (hg : f 0=0) (ht : Dormant h k) (v : Fin k→X) :
    iteratedFDeriv ℝ k (h ∘ f) 0 v=iteratedFDeriv ℝ k h 0 (fun i=> fderiv ℝ f 0 (v i)) := by
  let g:=fderiv ℝ f 0
  have hm : iteratedFDeriv ℝ k (h ∘ f) 0=iteratedFDeriv ℝ k (h ∘ g) 0 := by
    rw [iteratedFDeriv_comp (hg.symm ▸ hh) hf le_rfl, iteratedFDeriv_comp (show ContDiffAt ℝ k h (g 0) from map_zero g |>.symm ▸ hh) g.contDiff.contDiffAt le_rfl, hg,map_zero]
    refine Finset.sum_congr rfl fun c _ => ?_
    rcases c.length_le.eq_or_lt with he|he
    · have hz m (hv : m=1) : iteratedFDeriv ℝ m f 0=iteratedFDeriv ℝ m g 0 := by
        subst m; ext1 v; simp [g.fderiv]; rfl
      simp only [FormalMultilinearSeries.compAlongOrderedFinpartition,ftaylorSeries]
      rw [show (fun i=>iteratedFDeriv ℝ (c.partSize i) f 0) = fun i=>iteratedFDeriv ℝ (c.partSize i) g 0 from
        funext fun i=>hz _ (atomDegree c he i)]
    apply ContinuousMultilinearMap.ext; intro d
    simp only [FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, ht c.length he]; rfl
  rw [hm,rightLog h g hh]; rfl

lemma leading_comp (h : Y→Z) (f : X→Y) (hh : ContDiffAt ℝ k h 0) (hf : ContDiffAt ℝ k f 0)
    (hg : f 0=0) (ht : Dormant h k) (v : Fin k→X) :
    coeff (h ∘ f) k 0 v=coeff h k 0 (fun i=> fderiv ℝ f 0 (v i)) := by
  simp only [coeff, smul_apply,wakes h f hh hf hg ht]

end YM.Progress.ClassicalKin
