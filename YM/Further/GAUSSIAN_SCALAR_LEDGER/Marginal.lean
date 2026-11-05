import YM.Further.GAUSSIAN_SCALAR_LEDGER.Gaussian

set_option warningAsError false

/-!
# Schur complements if taking Gaussian-sector marginals

Use IF F0/mean/C data already priced on this sector; don't
make Y-dependent marginals into separate tags. The block being
integrated out contributes `sqrt(det A11)⁻¹` when *not*
normalizing. In the normalized Gaussian this factor goes towards
the correctly normalized retained marginal. Its precision
is generally not the restriction of the original precision.
Even the map-to-fewer-letters is on the one whole Gaussian.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.GaussianScalar
namespace Marginal

open Function MeasureTheory Matrix Set
open scoped Topology ENNReal BigOperators

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable (W : Wall (ι ⊕ κ))

def a11 := W.submatrix Sum.inl Sum.inl
def d22 := W.submatrix Sum.inr Sum.inr
def cross := W.submatrix Sum.inl Sum.inr

def eliminate := d22 W-(cross W)ᵀ*(a11 W)⁻¹*cross W

variable {W} (h : W.PosDef)
include h

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma also_pos : (a11 W).PosDef := h.submatrix Sum.inl_injective

omit [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
lemma viewed : W= fromBlocks (a11 W) (cross W) (cross W)ᴴ (d22 W) := by
  ext i j
  cases i <;> cases j <;> first | rfl | exact (congr_fun (congr_fun h.1.eq _) _).symm

lemma pen_cost : W.det = (a11 W).det * (eliminate W).det := by
  letI : Invertible (a11 W) := (also_pos h).isUnit.invertible
  calc
    _ = _ := congr_arg Matrix.det (viewed h)
    _ = _ := by rw [det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]; rfl

omit [DecidableEq κ] in
lemma eliminated_pos : (eliminate W).PosDef := by
  letI : Invertible (a11 W) := (also_pos h).isUnit.invertible
  have hh : (fromBlocks (a11 W) (cross W) (cross W)ᴴ (d22 W)).PosDef := (viewed h) ▸ h
  have hv : IsHermitian (eliminate W) :=
    ((Matrix.PosDef.fromBlocks₁₁ _ _ (also_pos h)).mp hh.posSemidef).1
  apply PosDef.of_dotProduct_mulVec_pos hv
  intro x hx
  let y : VV ι := -(((a11 W)⁻¹ * cross W) *ᵥ x)
  have hz : Sum.elim y x ≠ (0:VV (ι⊕κ)) := fun he => hx (funext fun i => congr_fun he (Sum.inr i))
  have he := (posDef_iff_dotProduct_mulVec.mp hh).2 hz
  rw [dotProduct_mulVec,Matrix.schur_complement_eq₁₁ _ _ _ _ (also_pos h).1,
    show y+_=0 from neg_add_cancel _,← dotProduct_mulVec, star_zero, zero_dotProduct,zero_add,←dotProduct_mulVec] at he
  exact he

lemma marginal_inverse : d22 W⁻¹ = (eliminate W)⁻¹ := by
  let E := a11 W; let D := d22 W; let B := cross W
  let L := fromBlocks E B Bᴴ D
  have he : W=L := viewed h
  have hp : E.PosDef := also_pos h
  have hb : L.PosDef := he ▸ h
  letI : Invertible E := hp.isUnit.invertible
  letI : Invertible L := hb.isUnit.invertible
  have ht : D-Bᴴ * ⅟E * B = eliminate W := by rw [Matrix.invOf_eq_nonsing_inv]; rfl
  letI : Invertible (D-Bᴴ * ⅟E * B) := (show IsUnit (D-Bᴴ * ⅟E * B) by rw [ht]; exact (eliminated_pos h).isUnit).invertible
  have hv := invOf_fromBlocks₁₁_eq E B Bᴴ D
  -- inverse inside nested invertible instances
  have hs : d22 (⅟L) = ⅟(D-Bᴴ*⅟E*B) := by
    change d22 (⅟(fromBlocks E B Bᴴ D))=_; rw [hv]; rfl
  rw [invOf_eq_nonsing_inv,invOf_eq_nonsing_inv (D-Bᴴ*⅟E*B),ht] at hs
  calc
    d22 W⁻¹ = d22 L⁻¹ := by rw [he]
    _ = _ := hs



lemma PDF (x : VV ι) (y : VV κ) :
    lawPDF W⁻¹ (Sum.elim x y) = lawPDF (a11 W)⁻¹ (x + ((a11 W)⁻¹*cross W) *ᵥ y) * lawPDF (d22 W⁻¹) y := by
  let X := Sum.elim x y
  let z := x+((a11 W)⁻¹*cross W) *ᵥ y
  let E := eliminate W
  let L := a11 W
  have he : E.PosDef := eliminated_pos h
  have hl : L.PosDef := also_pos h
  letI : Invertible W := h.isUnit.invertible
  letI : Invertible L := hl.isUnit.invertible
  letI : Invertible E := he.isUnit.invertible
  have hh : X ⬝ᵥ (W*ᵥX)=z ⬝ᵥ (L*ᵥ z) + y ⬝ᵥ (E*ᵥ y) := by
    conv_lhs => rw [viewed h]
    have hw := Matrix.schur_complement_eq₁₁ (cross W) (d22 W) x y hl.1
    simp only [← dotProduct_mulVec,star_trivial] at hw
    exact hw
  have hh' : W⁻¹.det = L⁻¹.det * E⁻¹.det := by
    rw [det_nonsing_inv,det_nonsing_inv,det_nonsing_inv, pen_cost h, Ring.inverse_eq_inv,Ring.inverse_eq_inv,Ring.inverse_eq_inv, _root_.mul_inv_rev,mul_comm]
  have hx : modeCost W⁻¹=modeCost L⁻¹ * modeCost E⁻¹ := by
    unfold modeCost; rw [Fintype.card_sum,pow_add,hh',Real.sqrt_mul (x := L⁻¹.det) (by exact hl.inv.det_pos.le)]; ring
  change lawPDF W⁻¹ X= lawPDF L⁻¹ z*_
  rw [marginal_inverse h]
  change _ = _ * lawPDF E⁻¹ y
  unfold lawPDF; rw [Matrix.inv_inv_of_invertible W, Matrix.inv_inv_of_invertible E,
      Matrix.inv_inv_of_invertible L,hx, hh, neg_add_rev,add_div,Real.exp_add]; field_simp

lemma split_kernel (f : VV (ι⊕κ) → ℝ) (hi : Integrable f (fieldLaw W⁻¹)) :
    let M : VV κ → VV ι := fun y => ((a11 W)⁻¹*cross W) *ᵥ y
    (∀ᵐ y ∂(volume : Measure (VV κ)), Integrable (fun x => f (Sum.elim (x-M y) y)) (fieldLaw (a11 W)⁻¹)) ∧
    Integrable (fun y => ∫ x, f (Sum.elim (x-M y) y) ∂fieldLaw (a11 W)⁻¹) (fieldLaw (d22 W⁻¹)) ∧
    (∫ x, f x ∂fieldLaw W⁻¹) =
      ∫ y, ∫ x, f (Sum.elim (x-M y) y) ∂fieldLaw (a11 W)⁻¹ ∂fieldLaw (d22 W⁻¹) := by
  intro M
  let g := fun x => lawPDF W⁻¹ x * f x
  have hg : Integrable g := (integrable_law h.inv f).mp hi
  let p : VV ι × VV κ ≃ᵐ VV (ι⊕κ) := (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι⊕κ => ℝ)).symm
  have hp : MeasurePreserving p volume volume := volume_measurePreserving_sumPiEquivProdPi_symm _
  have hx : Integrable (g ∘ p) ((volume : Measure (VV ι)).prod volume) :=
    (hp.integrable_comp_emb p.measurableEmbedding).mpr hg
  have hl : (a11 W).PosDef := also_pos h
  have hL : (d22 W⁻¹).PosDef := by rw [marginal_inverse h]; exact (eliminated_pos h).inv
  let k (x : VV ι) y := f (Sum.elim (x-M y) y)
  have he x y : g (p (x + -(M y),y)) = lawPDF (d22 W⁻¹) y * (lawPDF (a11 W)⁻¹ x * k x y) := by
    unfold g k
    rw [show p (x + - M y,y)=Sum.elim (x-M y) y by rw [← sub_eq_add_neg]; rfl,PDF h,show x-M y+_=x from sub_add_cancel ..]; ring
  have hw (y : VV κ) : (∫ x : VV ι, (g ∘ p) (x,y)) =
      lawPDF (d22 W⁻¹) y * ∫ x, k x y ∂fieldLaw (a11 W)⁻¹ := by
    rw [← integral_add_right_eq_self (μ:=volume) _ (-M y),integral_law hl.inv,← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => he x y)
  refine ⟨?_,?_,?_⟩
  · filter_upwards [hx.prod_left_ae] with y hy
    change Integrable (fun x => k x y) _
    have hz := (measurePreserving_add_right volume (-M y)).integrable_comp_emb
      ((Homeomorph.addRight (-M y)).measurableEmbedding) (g:=fun x => (g∘p) (x,y)) |>.mpr hy
    change Integrable (fun x => g (p (x+ -(M y),y))) _ at hz
    simp_rw [he] at hz
    exact (integrable_law hl.inv _).mpr ((integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (lawPDF_pos hL y).ne') _).mp hz)
  · apply (integrable_law hL _).mpr; change Integrable (fun y => lawPDF (d22 W⁻¹) y * ∫ x, k x y ∂fieldLaw _) _
    simp_rw [←hw]; exact hx.integral_prod_right
  rw [integral_law h.inv]; change (∫ x,g x) = ∫ y, ∫ x,k x y ∂fieldLaw _ ∂fieldLaw _
  rw [← hp.integral_comp p.measurableEmbedding g]
  change (∫ x,g (p x) ∂((volume : Measure (VV ι)).prod volume)) = _
  have hy := integral_prod_symm _ hx
  change (∫ x,g (p x) ∂((volume : Measure (VV ι)).prod volume)) = _ at hy
  rw [hy]; simp_rw [hw]; exact (integral_law hL _).symm

-- actual law on the retained Z's
lemma push_right : (fieldLaw W⁻¹).map (fun z : VV (ι⊕κ) => z ∘ Sum.inr) = fieldLaw (d22 W⁻¹) := by
  let p (z : VV (ι⊕κ)) := z ∘ Sum.inr
  have hp : Measurable p := measurable_pi_lambda _ fun _ => measurable_pi_apply _
  ext s hs
  change Measure.map p _ s = _
  rw [Measure.map_apply hp hs]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_lt_top _ _).ne (measure_lt_top _ _).ne).mp
  let f := s.indicator fun _ => (1:ℝ)
  let T := p ⁻¹' s
  have hT : MeasurableSet T := hp hs
  let g := T.indicator fun _ => (1:ℝ)
  have hi : Integrable g (fieldLaw W⁻¹) := (integrable_const 1).indicator hT
  have he := (split_kernel h g hi).2.2
  have hk x (y : VV κ) : g (Sum.elim x y) = f y := by
    have hh : p (Sum.elim x y)=y := rfl
    by_cases h : y∈s <;> simp [g,f,T,hh,h]
  simp_rw [hk,integral_const,probReal_univ, one_smul] at he
  simp only [g,f,integral_indicator_const _ hs, integral_indicator_const _ hT,smul_eq_mul, mul_one] at he
  exact he
end Marginal
end YM.Further.GaussianScalar
