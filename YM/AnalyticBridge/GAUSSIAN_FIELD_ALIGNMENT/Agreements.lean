import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Orthogonal
import YM.Next.FREE_KERNELS.Amend
import YM.Next.UV_STRESS.Fringe

set_option warningAsError false

/-!
# Exact coincidence rules and conversions back to the installed window matrices

Sufficient, not necessary, criteria. `Shell.pad` at two different layers
composes by restriction. In particular on the whole-response differentiability
region, install the *cut* free-affine primary (not the unmasked action
Hessian), with identity completion on remaining frozen and tree slots if
using it on the `raw` survey. The two position conventions still act
differently on that object! Include exact transport of the actual Gaussian
measures under block symmetries as well.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.GaussianFieldAlignment.Agreements
open Function Filter Set Matrix Lattice Wilson Precision RG Tree Pressure Pressure.Stores
open Next.SectorChange Next.SectorChange.Rows Gaussian Schur Relative FreeResolvent.Affine Orthogonal
open MeasureTheory ProbabilityTheory WithLp
open scoped Classical Topology BigOperators InnerProductSpace ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} (A : Stores S) (F : Forest S.ratio) (x : ℝ)

section matrices
variable {ι : Type} [Fintype ι] [DecidableEq ι] (P : ι → Set ι) (L : Gaussian.Table ι)

/-- No rolling proof required then. -/
lemma central (hL : L.PosDef) (hw : ∀ i,i∈P i) (ht : ∀ i j : ι, i∉P j → L⁻¹ i j=0) : per P L = L⁻¹ := by
  ext i j; by_cases he : i∈P j
  swap
  · rw [per_zero _ _ he,ht _ _ he]
  let D := principal L (P j)
  have hp : D.PosDef := hL.submatrix Subtype.val_injective
  let u := fun i : P j => L⁻¹ i.val j
  let e : P j → ι := (↑)
  have hx : FreeResolvent.insertion e *ᵥ u = fun i => L⁻¹ i j := by
    funext i; by_cases hi : i∈P j
    · exact FreeResolvent.insertion_at e u Subtype.val_injective ⟨i,hi⟩
    exact (FreeResolvent.insertion_misses _ _ i fun ⟨q,hq⟩ => hi (hq ▸ q.property)).trans (ht _ _ hi).symm
  let z : P j := ⟨j,hw j⟩
  have hv (k : P j) : (1:Gaussian.Table (P j)) k z = (1:Gaussian.Table ι) (k:ι) j := by
    simp only [Matrix.one_apply,show k=z ↔ k.val=j from Subtype.ext_iff]
  have hD : D *ᵥ u = (1:Gaussian.Table _).col z := by
    funext k
    rw [col_apply,hv]
    change ((L.submatrix e e)*ᵥ u) k = _
    rw [← FreeResolvent.at_compression,hx]; exact congr_fun (congr_fun (Matrix.mul_nonsing_inv _ (IsUnit.mk0 _ hL.det_pos.ne')) _) _
  rw [per_read _ _ (hw j) he]
  change D⁻¹ ⟨i,he⟩ z = u ⟨i,he⟩
  have hh : u = D⁻¹ *ᵥ ((1:Gaussian.Table _).col z) := by rw [← hD,mulVec_mulVec,Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ hp.det_pos.ne'),one_mulVec]
  rw [hh,show (D⁻¹ *ᵥ ((1:Gaussian.Table _).col z)) ⟨i,he⟩ = (D⁻¹ * (1:Gaussian.Table (P j))) ⟨i,he⟩ z from rfl,Matrix.mul_one]

lemma sym_central (hL : L.PosDef) (hw : ∀ i,i∈P i) (ht : ∀ i j : ι, i∉P j → L⁻¹ i j=0) : clouded P L = L⁻¹ := by
  have h := (Matrix.isHermitian_iff_isSymm.mp hL.isHermitian).inv.eq
  rw [clouded,central P L hL hw ht,h]; ext i j; change (1/2:ℝ)*(L⁻¹ i j + L⁻¹ i j)=_; ring
end matrices

theorem exact (T : Tube G S) (V : Config G c) (k : S.Choices) : let Q := Rows.gram T x V k (shots S x) A F
    Q.PosDef → 120 ≤ radiusB x → (∀ i j, i∉panels A F (x:=x) (G:=G) j ∩ mids A F x j → Q⁻¹ i j=0) →
      fog A F T x V k = Q⁻¹ ∧ middle A F x T V k=Q⁻¹ ∧ meanLog A F T x V k = middleLog A F x T V k := by
  intro Q hQ he hh
  have hp := per_self (boards A F G he)
  have hm := per_self (mids_bars A F x (G:=G) he)
  have hu i j (hi : i ∉ panels (x:=x) (G:=G) A F j) : Q⁻¹ i j = 0 :=  hh i j (fun h => hi h.1)
  have hv i j (hi : i ∉ mids (G:=G) A F x j) : Q⁻¹ i j = 0 :=  hh i j (fun h => hi h.2)
  exact ⟨sym_central _ _ hQ hp hu,sym_central _ _ hQ hm hv,by unfold meanLog middleLog; rw [central _ Q hQ hp hu,central _ Q hQ hm hv]⟩

/-- Two pads compose. `whole` of `FREE_RESOLVENT` only padded on trunks;
putting another pad around it is necessary when there are frozen links, and
doesn't retruncate any boundary row of the true Gram. No `flag` masks inside
the `Mid.cutView.inspect` after taking these pads. -/
lemma hierarchical (T : Tube G S) (k : S.Choices) {σ C Λ : ℝ} (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ C Λ) {B : Vec (Raw G c)} (hB : WholeNoise k B) :
    let Q := Rows.gram T x (represent (decode B)) k (shots S x) A F; let e := address A F x
    fill e Q = FreeResolvent.Shell.pad e (whole S F k T.high T.up (shorter (till x)) B) := by
  intro Q e
  let R := block S k T.high T.up (shorter (till x)) B; let L := freeTo G S F
  have he := affineCore A F x T k B h hB hT
  change Q=(R.submatrix L L).submatrix (live A F x) (live A F x) at he
  rw [← fill_pad, he, ← FreeResolvent.Shell.reaches L R]
  rfl

lemma installed (T : Tube G S) (k : S.Choices) {σ C Λ : ℝ} (h : S.patch.Branches S.kernel G)
    (hT : T.up.Bounds T.high σ C Λ) : ∀ᶠ B : Vec (Raw G c) in 𝓝 0,
    let V := represent (decode B); let Q := Rows.gram T x V k (shots S x) A F
    let e := address A F x
    let piM := (FreeResolvent.Mid.cutView G S (radiusB x)).inspect
      (FreeResolvent.Shell.pad e (whole S F k T.high T.up (shorter (till x)) B)) 0
    ∀ η : ℝ, 0 < η → Gapped Q η → 120 ≤ radiusB x → piM=fill e (per (mids A F x) Q) ∧ Relative.symPart piM=fill e (middle A F x T V k) := by
  filter_upwards [near_whole k h] with B hB
  intro V Q e piM η hη hh ht
  unfold piM; rw [← hierarchical A F x T k h hT hB]; obtain ⟨hu,hv,-⟩ := prescription A F x T V k hh hη ht; exact ⟨hu,hv⟩



section measure
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (O : ColorOrtho G α) (e : α ≃ β) (C : Gaussian.Table (β×G.ColorIndex))

private abbrev Space (G : Gauge) (α : Type) := EuclideanSpace ℝ (α×G.ColorIndex)
def changeCLM : Space G β →L[ℝ] Space G α := ({ toFun := fun v => toLp 2 (Orthogonal.move O e v.ofLp)
                                                map_add' := fun _ _ => congr_arg _ (Matrix.mulVec_add ..)
                                                map_smul' := fun _ _ => congr_arg _ (Matrix.mulVec_smul ..) } : Space G β →ₗ[ℝ] Space G α).toContinuousLinearMap
-- warp_cloud adapts the Gaussian mean step from Mathlib's measurePreserving_restrict₂_multivariateGaussian (Rémy Degenne and Etienne Marion). Copyright (c) 2026 Rémy Degenne. All rights reserved. Apache-2.0. See NOTICE.
-- equality of Gaussian distribution not merely equality almost surely of a characteristic coefficient.
theorem warp_cloud (hC : C.PosDef) : MeasurePreserving (Orthogonal.move O e) (cloud C) (cloud (warp O e C)) := by
  let L := changeCLM O e
  have hm (u v : Space G β) : inner ℝ (L u) (L v)=inner ℝ u v := by
    simp only [PiLp.inner_apply,RCLike.inner_apply, conj_trivial]; exact move_dot O e ..
  have hi (u : Space G β) : L.adjoint (L u) = u := ext_inner_right ℝ (fun v => (L.adjoint_inner_left v (L u)).trans (hm u v))
  have ht : (multivariateGaussian 0 C).map L = multivariateGaussian 0 (warp O e C) := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map,integral_id_multivariateGaussian,map_zero]; exact IsGaussian.integrable_id
    apply ContinuousLinearMap.ext; intro a; apply ContinuousLinearMap.ext; intro b
    rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_multivariateGaussian hC.posSemidef,covarianceBilin_multivariateGaussian (warp_pos O e C hC).posSemidef]
    obtain ⟨u,hu⟩ := move_surj O e a.ofLp; obtain ⟨v,hv⟩ := move_surj O e b.ofLp
    rw [show a=L (toLp 2 u) from congr_arg (toLp 2) hu.symm,show b=L (toLp 2 v) from congr_arg (toLp 2) hv.symm,hi,hi]; exact (warp_qf O e C u v).symm
  have hm : Measurable (Orthogonal.move O e) := by unfold Orthogonal.move; exact (acts_meas _).comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
  refine ⟨hm,?_⟩; rw [cloud,cloud,← ht,Measure.map_map (by fun_prop) L.continuous.measurable,Measure.map_map hm (by fun_prop)]; rfl
end measure
end YM.AnalyticBridge.GaussianFieldAlignment.Agreements
