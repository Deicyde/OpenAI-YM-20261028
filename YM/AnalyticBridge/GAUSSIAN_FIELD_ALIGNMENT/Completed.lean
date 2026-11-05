import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Relative
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Postal

set_option warningAsError false

/-!
# Exact counting completion comparison (e.g. to reach full tree keys)

This is NOT a new physical chart price for vacant links. Include Haar on Y
and price only the actually integrated regular exp-coordinates! Just supplies
a Gaussian space with independent standard coordinates and the exact pull of
the marginal/cross-window scalar and quadratic tests. Can thus legitimately
change to e.g. a full-tree window law without inverting after erroneously
erasing boundary rows or silently restricting its covariance.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Completed
open Function Filter Set Matrix MeasureTheory Lattice ProbabilityTheory
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Completion Next.SectorChange.Schur
open FreeResolvent (native insertion)
open scoped Topology BigOperators Classical ENNReal InnerProductSpace

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {c : Side}
  (p : β → Site c) (e : α ↪ β) {σ M η : ℝ}

local notation "Mat" α => Gaussian.Table α
variable {A : Mat α}

def complement (e : α ↪ β) : α ⊕ ↥((range e)ᶜ : Set β) ≃ β :=
    ((Equiv.ofInjective _ e.injective).sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ range e))
omit [Fintype β] [DecidableEq α] in
lemma first_eq (i : α) : complement e (.inl i) = e i := rfl

omit [Fintype β] [DecidableEq α] in
lemma sym (h : A.IsSymm) : (fill e A).IsSymm := by
  unfold Matrix.IsSymm fill; rw [transpose_add, transpose_mul, transpose_mul, FreeResolvent.Shell.undo,
    h.eq, transpose_transpose,Matrix.mul_assoc]

omit [DecidableEq α] in
lemma retract (A : Mat α) : (fill e A).submatrix e e = A := by
  have h := fill_read e A _ (first_eq e)
  ext i j; exact congr_fun (congr_fun h (.inl i)) (.inl j)

lemma gapped (h : Gapped A η) (hA : A.IsSymm) : Gapped (fill e A) (min η 1) := by
  let t := complement e
  have he : (Next.SectorChange.Completion.wide A (1:Mat ↥((range e)ᶜ : Set β))).submatrix t.symm t.symm = fill e A := by
    rw [← fill_read e A _ (first_eq e)]; ext i j; simp [t]
  rw [← he,Relative.gap_iff]; exact (Relative.gap_iff.mp (wide_gap hA h).2).submatrix t.symm t.symm.injective

lemma pours (h : Pours A (p ∘ e) (p ∘ e) σ M) : Pours (fill e A) p p σ (M+1) := by
  have he : ∀ {A : Mat α}, (native c).Rows (p ∘ e) (p ∘ e) σ M A →
      (native c).Rows p p σ M (FreeResolvent.Shell.slice e (fill e A)) := by
    intro A H
    let R := fill e A
    constructor; intro i
    by_cases h : i ∈ range e
    · obtain ⟨a,rfl⟩ := h
      simp_rw [FreeResolvent.Shell.slice_test]; simp only [mem_range_self,true_and]
      rw [← Finset.sum_subset (s₁:=Finset.univ.image e) (Finset.subset_univ _) (fun i _ hi => ?_),Finset.sum_image (g:=e) (fun _ _ _ _ h => e.injective h)]
      · simp_rw [if_pos (mem_range_self _)]
        have hx (a b : α) : fill e A (e a) (e b) = A a b := congr_fun (congr_fun (retract e A) a) b
        simp_rw [hx]; exact H.bound a
      have h : i ∉ range e := fun ⟨k,hk⟩ => hi (hk ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _))
      rw [if_neg h,abs_zero,mul_zero]
    simpa [FreeResolvent.Shell.slice_test,h] using ‹Pours ..›.pos
  have hu : (native c).Schur p p σ 1 (FreeResolvent.Shell.off e) := FreeResolvent.Cost.Schur.one.abs_le (by
    intro i j; rw [FreeResolvent.Shell.off_test,Matrix.one_apply]; split
    next h => rw [if_pos h.1]
    exact abs_zero.trans_le (abs_nonneg _))
  rw [show fill e A = FreeResolvent.Shell.pad e (fill e A) from by rw [← fill_pad, retract]]
  refine Relative.to_pours ((FreeResolvent.Cost.Schur.mk (he (Relative.of_pours h).rows) ?_).add hu) (by linarith [h.pos])
  rw [FreeResolvent.Shell.sliced,transpose_mul,transpose_mul,transpose_transpose, retract,
    ← Matrix.mul_assoc, ← retract e A.transpose, ← FreeResolvent.Shell.sliced]
  exact he (Relative.of_pours h).cols



lemma per_fill' (P : β → Set β) (hw : ∀ i, i∈P i) (Q : Mat α) {η : ℝ} (hQ : Q.IsSymm) (he : 0 < η) (hg : Schur.Gapped Q η) :
    Schur.per P (fill e Q) = fill e (Schur.per (fun i => e ⁻¹' P (e i)) Q) := per_fill _ hw _ _ hQ he hg _ (first_eq e)

omit [DecidableEq α] in
lemma symPart_fill (Q : Mat α) : Relative.symPart (fill e Q) = fill e (Relative.symPart Q) := sym_fill _ _ _ (first_eq e)
-- marginal adapts the Gaussian coordinate marginal proof from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
-- Mathlib's restrict₂_multivariateGaussian argument, at an arbitrary address inclusion to coordinate functions.
private def projection : EuclideanSpace ℝ β →L[ℝ] EuclideanSpace ℝ α := LinearMap.toContinuousLinearMap
  { toFun := fun v => WithLp.toLp 2 (fun i => v (e i))
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
lemma marginal {C : Mat β} (hC : C.PosSemidef) : MeasurePreserving (fun a : Vec β => a ∘ e) (cloud C) (cloud (C.submatrix e e)) := by
  let L := projection e
  have he (i : α) (v : EuclideanSpace ℝ β) : L v i = v (e i) := rfl
  have ht : (multivariateGaussian 0 C).map L = multivariateGaussian (L 0) (C.submatrix e e) := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map,integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun α ℝ).toBasis fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,covarianceBilin_apply_eq_cov, covariance_map]
    · have hh (i : α) : (fun u => inner ℝ ((EuclideanSpace.basisFun α ℝ).toBasis i) u) ∘ L =
          fun u : EuclideanSpace ℝ β => u (e i) := by funext u; simp [PiLp.inner_apply,he]
      rw [hh,hh,covariance_eval_multivariateGaussian hC,covarianceBilin_multivariateGaussian (hC.submatrix _)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · exact L.continuous.measurable.aemeasurable
    · exact IsGaussian.memLp_two_id
  have hm : Measurable (fun a : Vec β => a ∘ e) := measurable_pi_lambda _ fun i => measurable_pi_apply _
  have hi (α : Type) [Fintype α] : Measurable (WithLp.ofLp : EuclideanSpace ℝ α → Vec α) := by fun_prop
  refine ⟨hm,?_⟩
  rw [cloud,cloud,← map_zero L, ← ht, Measure.map_map (hi α) L.continuous.measurable,Measure.map_map hm (hi β)]; rfl

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]



end YM.AnalyticBridge.GaussianFieldAlignment.Completed
