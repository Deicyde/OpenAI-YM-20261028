import YM.Next.EXTRACTION.Relay
import YM.Push.RELAY_MARK.Cutoff

/-!
# A uniformly affordable presentation for extraction

Not putting the equation space itself as the *range*: the extraction
interface wants equations in the kernel. Choose with period-uniform norm
(not from the similarity through `terminal` which could lose this). These latter requirements are used only
from ref onward; if padding, not imposing covariance of the factory on small cutoffs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Mark
open Function MeasureTheory Filter Labels Wilson Source Lattice RG Bid
open Extraction Extraction.Lease Next.Extract
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators InnerProductSpace
variable {G : Gauge} {C : Family G} {d p N : ℕ} {B : Frame G d}

-- Kernel projector conditions.
structure Chosen (B : Frame G d) (W : Submodule ℂ B.Coeff) (F : B.Coeff →L[ℂ] B.Coeff) : Prop where
  to_zero (x) : x∈W → F x=0
  id_sub (x) : x-F x∈W

namespace Chosen
variable {U : Submodule ℂ B.Coeff} {F : B.Coeff →L[ℂ] B.Coeff}

lemma stable (h : Chosen B U F) (x) : F (F x)=F x := by
  have he := h.to_zero (x-F x) (h.id_sub x); rw [map_sub,sub_eq_zero] at he; exact he.symm

lemma ker (h : Chosen B U F) : LinearMap.ker F.toLinearMap=U := le_antisymm (fun x hx=> by
  have he := h.id_sub x; rw [show F x=0 from LinearMap.mem_ker.mp hx,sub_zero] at he; exact he)
  (fun x hx=> LinearMap.mem_ker.mpr (h.to_zero x hx))

end Chosen

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

section Symmetry

def travelH (B : Frame G d) (s : Signed) := LinearMap.toContinuousLinearMap (B.act s.ortho)
lemma travel_at_mul (B : Frame G d) (s t : Signed) (x) : travelH B (s*t) x=travelH B s (travelH B t x) := by
  unfold travelH; simp only [show (s*t).ortho=s.ortho*t.ortho from map_mul Signed.inclusionO ..]; exact B.act_mul ..
lemma travel_at_one (B : Frame G d) (x) : travelH B 1 x=x := by
  change B.act _ _=x; rw [show (1:Signed).ortho=1 from map_one Signed.inclusionO,B.act_one]
lemma travel_at_inv (B : Frame G d) (s : Signed) (x) : travelH B s (travelH B s⁻¹ x)=x := by rw [← travel_at_mul, mul_inv_cancel, travel_at_one]
lemma travel_at_star (B : Frame G d) (s : Signed) (x) : travelH B s (star x)=star (travelH B s x) := by
  have hv (p) : B.coords (realBar p)=star (B.coords p) := by
    funext i; have h := B.conj_basis (B.coords p) i; rw [LinearEquiv.symm_apply_apply] at h; exact h
  obtain ⟨p,rfl⟩ := B.coords.surjective x
  change B.act _ _=star (B.act _ _); rw [← hv,B.act_coords,B.act_coords, ← real_turn,hv]

structure Active (B : Frame G d) (U : Submodule ℂ B.Coeff) : Prop where
  signed (s : Signed) x : x∈U → travelH B s x∈U
  real_ x : x∈U → star x∈U

structure Symmetry (B : Frame G d) (F : B.Coeff →L[ℂ] B.Coeff) : Prop where
  signed (s : Signed) x : F (travelH B s x)=travelH B s (F x)
  real_ x : F (star x)=star (F x)

private lemma stage_seat (B : Frame G d) : ∃ M : ℝ, 0<M ∧ ∀ U : Submodule ℂ B.Coeff,
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
end Symmetry

section Seats

/-- Precisely chosen projection data side for this proof, independent of order or history proofs. -/
structure Purse (C : Family G) (R : Weave G) (b : Presentation C) : Prop where
  pure (d N p : ℕ) : Chosen (C.labels.level d) (carrier C R d N p) (b.step d (N,p))
  pays (d : ℕ) : ∃ x : ℝ, 0<x ∧ ∀ N p, ‖b.step d (N,p)‖ ≤ x
  shows (d N p : ℕ) : Active (C.labels.level d) (carrier C R d N p) → Symmetry (C.labels.level d) (b.step d (N,p))

theorem present (C : Family G) (R : Weave G) : ∃ b, Purse C R b := by
  classical
  choose M hm h using fun d=> stage_seat (C.labels.level d)
  choose F hf hv hs using fun d (b : ℕ × ℕ)=> h d (carrier C R d b.1 b.2)
  exact ⟨⟨F,fun d b=> (hf d b).stable⟩,fun d N p=> hf d (N,p),fun d=>⟨M d,hm d,fun N p=>hv d (N,p)⟩,fun d N p=>hs d (N,p)⟩

variable {R : Weave G} {b : Presentation C}


lemma active (h : C.Makes) (H : Portfolio C.params (C.localSection d) (R d)) (hp : C.ref d≤N) : Active (C.labels.level d) (carrier C R d N p) := by
  constructor
  · intro s x hx; obtain ⟨y,hy,rfl⟩ := obtained R _ hx
    change (C.labels.level d).act s.ortho _∈_
    rw [← embed_signed R h H hp]; exact entry_mem _ _ _ _ _ _ (turn_ideal _ hy)
  intro x hx; obtain ⟨y,hy,rfl⟩ := obtained R _ hx
  rw [← embed_real R h H hp]; exact entry_mem _ _ _ _ _ _ (conjugate_ideal hy)
end Seats
end YM.Push.Mark
