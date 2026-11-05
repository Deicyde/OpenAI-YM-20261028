import YM.Push.RELAY_MARK.Step
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p N : ℕ} {B : Frame G d}

private lemma seat (B : Frame G d) : ∃ M : ℝ, 0<M ∧ ∀ U : Submodule ℂ B.Coeff,
    ∃ F, Chosen B U F ∧ ‖F‖ ≤ M := by
  let A : EuclideanSpace ℂ B.Index ≃ₗ[ℂ] B.Coeff := WithLp.linearEquiv _ _ _
  let Q := A.toContinuousLinearEquiv
  let W := Q.toContinuousLinearMap
  let V := Q.symm.toContinuousLinearMap
  let X := ContinuousLinearMap.id ℂ B.Coeff
  refine ⟨1+‖X‖+‖W‖*‖V‖,by positivity,fun U=>?_⟩
  let P := U.comap W.toLinearMap
  let R := P.starProjection
  let Y := W.comp (R.comp V)
  have hv (x) : W (V x)=x := Q.apply_symm_apply x
  refine ⟨X-Y,⟨?_,?_⟩,?_⟩
  · intro u hu
    have he : V u∈P := Submodule.mem_comap.mpr ((hv u).symm ▸ hu)
    rw [sub_apply]; change u-W (P.starProjection (V u))=0
    rw [Submodule.starProjection_eq_self_iff.mpr he,hv,sub_self]
  · intro u; change u-(u-Y u)∈U
    rw [sub_sub_cancel]
    exact Submodule.mem_comap.mp (P.starProjection_apply_mem (V u))
  have he : ‖R‖ ≤ 1 := R.opNorm_le_bound zero_le_one fun x=> by simpa using P.norm_starProjection_apply_le x
  have hy : ‖Y‖ ≤ ‖W‖*‖V‖ := W.opNorm_comp_le (R.comp V) |>.trans <| mul_le_mul_of_nonneg_left
    ((ContinuousLinearMap.opNorm_comp_le R V).trans (mul_le_of_le_one_left (norm_nonneg _) he)) (norm_nonneg _)
  linarith [norm_sub_le X Y]
lemma potage (B : Frame G d) : ∃ M : ℝ, 0<M ∧ ∀ U : Submodule ℂ B.Coeff,
    ∃ F, Chosen B U F ∧ ‖F‖ ≤ M ∧ (Active B U → Symmetry B F) := by
  obtain ⟨x,hx,hb⟩ := seat B
  let W := Work.G06.share
  let V := travelH B
  let c : ℂ := (2:ℂ)⁻¹
  let A := ‖W‖ * ∑ i : Signed, ‖V i‖ * (x * ‖V i⁻¹‖)
  let a := ‖c‖*(A+A)
  refine ⟨max x a,hx.trans_le (le_max_left ..),fun U=>?_⟩
  obtain ⟨F,hF,hf⟩ := hb U
  by_cases hu : Active B U
  swap; · exact ⟨F,hF,hf.trans (le_max_left ..), fun h=>(hu h).elim⟩
  let Y (i : Signed) := (V i) ∘L F ∘L V i⁻¹
  let Q := W • ∑ i,Y i
  have hQ : Chosen B U Q := by
    have hi (p) : Q p= W • (∑ i,Y i p) := by simp only [Q,smul_apply,sum_apply]
    constructor
    · intro p hp; rw [hi, Finset.sum_eq_zero _,smul_zero]
      intro i _; unfold Y; simp only [ContinuousLinearMap.comp_apply]
      rw [hF.to_zero _ (hu.signed i⁻¹ p hp),map_zero]
    intro p
    have hv : p-Q p= W • ∑ i,(p-Y i p) := by rw [Finset.sum_sub_distrib,smul_sub,Work.G06.share_sum, hi]
    rw [hv]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _=>?_)
    change p - (V i) (F ((V i⁻¹) p))∈_
    nth_rw 1 [← travel_at_inv B i p]; rw [← map_sub]; exact hu.signed i _ (hF.id_sub _)
  have hB (i : Signed) p : Q (V i p)=V i (Q p) := by
    have ht (s : Signed) : Y (i*s) (V i p)=V i (Y s p) := by
      dsimp only [Y,ContinuousLinearMap.comp_apply, V]; rw [← travel_at_mul, mul_inv_rev, mul_assoc,inv_mul_cancel,
        mul_one,travel_at_mul]
    dsimp only [Q]; rw [smul_apply,smul_apply,map_smul,sum_apply,sum_apply, map_sum]
    simp_rw [← ht]; exact congr_arg (W • ·) (Equiv.sum_comp (Equiv.mulLeft i) (fun t=> Y t (V i p))).symm
  let R : B.Coeff →L[ℂ] B.Coeff := LinearMap.toContinuousLinearMap
    ({toFun := fun p:B.Coeff=> star (Q (star p)), map_add' := by simp,
      map_smul' := fun t p => by simp only [star_smul,map_smul,star_star]; rfl} : B.Coeff→ₗ[ℂ] B.Coeff)
  let k : B.Coeff→L[ℂ]B.Coeff := c • (Q+R)
  have he (p : B.Coeff) : R p= star (Q (star p)) := rfl
  have hC (p : B.Coeff) : k p=c • (Q p+star (Q (star p))) := by rw [← he]; dsimp only [k]; rw [smul_apply,add_apply]
  refine ⟨k,⟨?_,?_⟩,?_ ,fun _=>⟨?_,?_⟩⟩
  · intro p hp; rw [hC,hQ.to_zero p hp,hQ.to_zero _ (hu.real_ _ hp)]; simp
  · intro p
    have ht : p - star (Q (star p))∈U := by
      have h := hu.real_ _ (hQ.id_sub (star p)); simpa only [star_sub,star_star] using h
    have hv : p-k p=c • ((p-Q p)+(p-star (Q (star p)))) := by
      rw [hC, ← add_sub_add_comm, ← two_smul ℂ, smul_sub, smul_smul, inv_mul_cancel₀ (two_ne_zero),one_smul]
    rw [hv]; exact U.smul_mem c (U.add_mem (hQ.id_sub _) ht)
  · have hq : ‖Q‖ ≤ A := by
      unfold Q A; rw [norm_smul]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (Finset.sum_le_sum (fun i _=>?_))) (norm_nonneg _)
      apply le_trans ((V i).opNorm_comp_le (F.comp (V i⁻¹)))
      exact mul_le_mul_of_nonneg_left ((F.opNorm_comp_le _).trans (mul_le_mul_of_nonneg_right hf (norm_nonneg _))) (norm_nonneg _)
    have hr : ‖R‖ ≤ A := R.opNorm_le_bound ((norm_nonneg Q).trans hq) fun p=>by
      rw [he,norm_star]
      apply (Q.le_opNorm _).trans
      rw [norm_star]; exact mul_le_mul_of_nonneg_right hq (norm_nonneg _)
    apply le_trans ?_ (le_max_right x _)
    unfold k; rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ((norm_add_le ..).trans (add_le_add hq hr)) (norm_nonneg _)
  · intro i p; rw [hC,hC,← travel_at_star,hB,hB,map_smul,map_add,travel_at_star]
  intro p; rw [hC,hC,star_star,star_smul,star_add,star_star,add_comm (Q (star p)),
    show star c=c by change (starRingEnd ℂ) c=_; unfold c; rw [map_inv₀, show (2:ℂ)=1+1 by norm_num,map_add,map_one]]
end YM.Push.Mark
