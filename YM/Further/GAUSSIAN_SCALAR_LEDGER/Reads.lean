import YM.Further.GAUSSIAN_SCALAR_LEDGER.Inactive
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Marginal
import YM.Work.B13


set_option warningAsError false

/-! # Consistency between full-coordinate and regular-only readings

Don't need inactive Gaussian factors in the balance. If wanting
to complete the **Z** law with A,C matrices (Y still separately on
actual Haar!), here are exact marginal connections. The Frco exponent
charged in full-position ordered products pays the one inside the real
changes, including arbitrary centering.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar.Reads

open Matrix Function Filter MeasureTheory Set Precision SectorNext.Vacuum Lattice RG Tree
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
section
variable {ι ω : Type*} [Fintype ι] [Fintype ω] (e : ι ≃ ω)

-- counting convention
lemma cut_quad (x y : VV ω) : dotProduct x y= dotProduct (x∘⇑e) (y∘⇑e) :=
  (Equiv.sum_comp e (fun i => x i*y i)).symm
lemma legs (K : Wall ω) (x : VV ω) : (K *ᵥ x) ∘ ⇑e = (K.submatrix e e)*ᵥ(x∘⇑e) := by
  rw [Matrix.submatrix_mulVec_equiv]; rw [show (x ∘ ⇑e) ∘ ⇑e.symm = x from funext (by intro i; simp)]

variable [DecidableEq ι] [DecidableEq ω]

lemma bonds {C : Wall ω} (z : VV ω) : lawPDF (C.submatrix e e) (z∘⇑e) = lawPDF C z := by
  unfold lawPDF modeCost
  rw [Fintype.card_congr e, Matrix.det_submatrix_equiv_self, inv_submatrix_equiv,←legs,
    ← cut_quad]

lemma pushing (C : Wall ω) (h : C.PosDef) :
    (fieldLaw (C.submatrix e e)).map (MeasurableEquiv.piCongrLeft (fun _ : ω => ℝ) e)=fieldLaw C := by
  let g := MeasurableEquiv.piCongrLeft (fun _ : ω => ℝ) e
  have he : MeasurePreserving g volume volume := volume_measurePreserving_piCongrLeft _ _
  rw [fieldLaw_density h,fieldLaw_density (h.submatrix e.injective)]
  ext s hs; rw [Measure.map_apply g.measurable hs,withDensity_apply _ (g.measurable hs), withDensity_apply _ hs]
  let F := fun y => ENNReal.ofReal (lawPDF C y)
  have hw := setLIntegral_map (μ:=volume) hs (f:=F) (lawPDF_cont C).measurable.ennreal_ofReal g.measurable
  rw [he.map_eq] at hw
  rw [hw]
  apply setLIntegral_congr_fun (g.measurable hs); intro x _
  have hx : g x ∘ ⇑e = x := funext (Equiv.piCongrLeft_apply_apply (fun _ : ω=>ℝ) e x)
  have hb := bonds (C:=C) e (g x)
  rw [hx] at hb
  exact congr_arg _ hb

-- reindex followed by projection (fast dropped)
theorem reads {τ π : Type*} [Fintype τ] [DecidableEq τ] [Fintype π] [DecidableEq π]
    (e : τ⊕π ≃ ω) (C : Wall ω) (h : C.PosDef) :
    let r := ⇑e ∘ Sum.inr
    (fieldLaw C).map (fun z : VV ω => z∘r) = fieldLaw (C.submatrix r r) := by
  intro r
  let g (z : VV ω) := z∘r
  have he : Measurable g := measurable_pi_lambda _ fun i => measurable_pi_apply _
  let Y := MeasurableEquiv.piCongrLeft (fun _ : ω => ℝ) e
  let M := C.submatrix e e
  have hh : M.PosDef := h.submatrix e.injective
  letI : Invertible M := hh.isUnit.invertible
  have hp := Marginal.push_right hh.inv
  rw [Matrix.inv_inv_of_invertible M] at hp
  change Measure.map g _ = _
  rw [← pushing e C h, Measure.map_map he Y.measurable]
  have hr : g ∘ ⇑Y = fun z => z ∘ Sum.inr := by
    funext z i; exact Equiv.piCongrLeft_apply_apply _ _ _ _
  rw [hr]; exact hp
end

variable {G : Gauge} {c f : Side} {g : Ratio c f} {F : Forest g} (H : Finset F.Free)

def holdBits (b : VV (Key F G)) (i : Hold G H) := b (mergeBits H G (Sum.inr i))

lemma budget (A : Wall (Bits G H)) (x : VV (Key F G)) :
    x ⬝ᵥ (filled H A *ᵥ x) = viewBits H x ⬝ᵥ (A *ᵥ viewBits H x) + holdBits H x ⬝ᵥ holdBits H x := by
  let e := mergeBits H G
  rw [cut_quad e, legs e,show (filled H A).submatrix e e=_ from sortBits H A 1,Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec,Matrix.zero_mulVec, Matrix.one_mulVec,zero_add, add_zero]
  exact Fintype.sum_sum_type _


set_option synthInstance.maxSize 2048









omit H
section actual
variable {S : StepData c f} {F : Forest S.ratio} {O : ChartRatio G} {ρ : Type*} [Fintype ρ]
variable (v : Fiber F O ρ) (L : Lens (Key F G)) (Y : Frozen v.H G)


end actual
end YM.Further.GaussianScalar.Reads
