import YM.Next.MAXWELL.Fock
import YM.Next.MAXWELL.Strict


/-!
# Factoring the reflected leg kernel
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell.Free
open Set Function Filter Tensor Analysis MeasureTheory Fock
open scoped ContDiff Topology BigOperators InnerProductSpace ComplexOrder

variable {G : Gauge} {σ : Type*} [Fintype σ] {j l : ℕ}

def bottomEntry (a : Axis) (p : Limb G) : Limb G :=
  (through a p.1, ⟨p.2.1,probeTurn (Signed.reflect a) p.2.2⟩)

lemma link_ray (a : Axis) (p q : Limb G) : linkEntry (bottomEntry a p) (bottomEntry a q) = star (linkEntry p q) := by
  by_cases he : p.1=q.1
  · unfold bottomEntry; rw [he,link_zero, show linkEntry p q=0 from if_pos he, star_zero]
  rw [show linkEntry p q = _ from if_neg he, bottomEntry,bottomEntry, link_eq (through a p.1) (through a q.1) _ _ ((Ortho.move_injective _).ne he)]
  dsimp only [through]; rw [show K _ _ _ _ = _ from K_orientation (Signed.reflect a) p.2.2 q.2.2 he]; simp

lemma gram_sym (p q : Limb G) (a : Axis) (hp : 0 < p.1 a) (hq : 0 < q.1 a) :
    K p.2.2 (probeTurn (Signed.reflect a) q.2.2) p.1 (through a q.1) =
      K q.2.2 (probeTurn (Signed.reflect a) p.2.2) q.1 (through a p.1) := by
  have he : p.1≠through a q.1 := by intro h; rw [h,after] at hp; linarith
  let s := Signed.reflect a
  rw [← K_orientation s _ _ he]
  have ht : probeTurn s (probeTurn s q.2.2) = q.2.2 := by dsimp only [s]; nth_rw 2 [← mirrored_inv a]; exact probe_inv_turn ..
  have hz : Ortho.move s (through a q.1) = q.1 := by dsimp only [s,through]; nth_rw 2 [← mirrored_inv a]; exact Ortho.move_inv ..
  rw [ht,hz,K_symmetric _ _ (show Ortho.move s p.1≠q.1 from fun h => by
    have ht : through a p.1=q.1 := h; rw [← ht,after] at hq; linarith)]; rfl

namespace Factorization
variable (a : Axis) (P : σ → Limb G)

def mat : Matrix σ σ ℝ := Matrix.of fun i j => K (P i).2.2 (probeTurn (Signed.reflect a) (P j).2.2) (P i).1 (through a (P j).1)

variable (H : ∀ i, 0 < (P i).1 a)
include H
lemma mat_form (x : σ → ℝ) : dotProduct (star x) ((mat a P).mulVec x) =
    heatLevel a (fun i => (P i).1) (fun i => x i • (P i).2.2) 0 := by
  unfold Matrix.mulVec dotProduct mat; simp only [Finset.mul_sum,Matrix.of_apply,star_trivial]
  unfold heatLevel floated; simp only [zero_smul,add_zero]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hi := H i
  have hx : (P i).1 ≠ through a (P j).1 := by intro h; rw [h,after] at hi; linarith [H j]
  rw [K_pairing _ _ hx,K_pairing _ _ hx,map_smul,map_smul,map_smul, LinearMap.smul_apply]
  change x i * (_ * x j) = x j * (x i * _); ring

lemma mat_good : (mat a P).PosSemidef := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨Matrix.ext (fun i j => (show mat a P j i = mat a P i j from gram_sym (P j) (P i) a (H j) (H i))),
    fun x => ?_⟩
  -- star source included in matrix ordering
  rw [mat_form a P H]; exact reflected_positive _ _ _ H le_rfl

omit H in
lemma entry_match (L : Matrix σ σ ℝ) (h : mat a P = star L * L) i j (H : ∀ i, 0 < (P i).1 a) :
    linkEntry (bottomEntry a (P i)) (P j) = ∑ k : σ, star ((L k i:ℝ):ℂ) * ((L k j:ℝ):ℂ) := by
  have hi := H j
  have ht : (P j).1 ≠ through a (P i).1 := by intro h; rw [h,after] at hi; linarith [H i]
  rw [show linkEntry (bottomEntry a (P i)) (P j) = _ from if_neg (show (bottomEntry a (P i)).1 ≠ _ from Ne.symm ht)]
  change (K _ _ (through a (P i).1) (P j).1:ℂ)= _
  rw [K_symmetric _ _ ht.symm]
  change (mat a P j i : ℂ) = _
  rw [h,Matrix.mul_apply]
  simp_rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,star_trivial]; push_cast
  apply Finset.sum_congr rfl; intro k _; simp [mul_comm]

open scoped MatrixOrder in
lemma columns [DecidableEq σ] : ∃ L : Matrix σ σ ℝ, mat a P = star L * L := by
  exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (mat_good a P H).nonneg

end Factorization

open Factorization

/-- Already for any finite alphabet of one-point probes. -/
theorem coordGram (a : Axis) (x : E4) (hx : 0 < x a) (s : Finset (Slot G)) :
    (mat a fun i : s => ((x,coordF i.val) : Limb G)).PosDef := by
  classical
  let P := fun i : s => ((x,coordF i.val) : Limb G)
  change (mat a P).PosDef
  have H : ∀ i, 0 < (P i).1 a := fun _ => hx
  have hp := mat_good a P H
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hp.1, fun z hz => ?_⟩
  apply lt_of_le_of_ne (hp.dotProduct_mulVec_nonneg z)
  rw [mat_form a P H]; intro he
  let p := fun i : s => z i • coordinateLeg i.val
  have ht := level_detects a p x hx he.symm
  apply hz
  funext i; obtain ⟨⟨j,i⟩,hi⟩ := i
  let A : TaylorTower G := Function.update (fun i => 0) j (frame G j i)
  have ha := ht A
  rw [Finset.sum_eq_single_of_mem (a := (⟨⟨j,i⟩,hi⟩ : ↥s)) (Finset.mem_univ _)] at ha
  · change z (⟨⟨j,i⟩,hi⟩:↥s) * (frame G j).coord i (A j) = 0 at ha
    simpa [A] using ha
  rintro ⟨⟨k,u⟩,hk⟩ _ hh
  change z (⟨⟨k,u⟩,hk⟩:↥s) * (frame G k).coord u (A k)=0
  by_cases he : k=j
  · subst k; have hv : i≠u := fun he => hh (by subst u; rfl); simp [A,hv]
  simp [A,he]

section inject
variable [DecidableEq σ]

lemma synth_inj (L : Matrix σ σ ℝ) (h : IsUnit L) :
    Injective (MvPolynomial.aeval (R:=ℂ) (fun i : σ => synth fun j : σ => ((L j i : ℝ) : ℂ))) := by
  let g : σ → Space σ := fun i => synth fun j : σ => ((L j i : ℝ):ℂ)
  let f : Space σ →ₐ[ℂ] Space σ := MvPolynomial.aeval g
  let B : Matrix σ σ ℝ := ↑(h.unit⁻¹)
  let e : Space σ →ₐ[ℂ] Space σ := MvPolynomial.aeval fun i => synth fun j => ((B j i : ℝ):ℂ)
  have he : B*L=1 := by exact h.unit.inv_mul
  have ht : e.comp f = AlgHom.id ℂ (Space σ) := by
    ext1 i
    change e (f (MvPolynomial.X i)) = MvPolynomial.X i
    simp only [f, MvPolynomial.aeval_X, e,g,synth,map_sum,map_mul, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq]
    simp_rw [Finset.mul_sum,← mul_assoc]
    rw [Finset.sum_comm]; simp_rw [← Finset.sum_mul,← map_mul,← Complex.ofReal_mul,← map_sum,← Complex.ofReal_sum]
    have hh (j : σ) : ∑ k : σ, L k i * B j k = if j=i then 1 else 0 := by
      rw [show (∑ k : σ, L k i * B j k) = (B*L) j i from Finset.sum_congr rfl fun k _ => mul_comm .., he, Matrix.one_apply]
    simp [hh,apply_ite,ite_mul]
  exact (show LeftInverse e f from fun x => DFunLike.congr_fun ht x).injective
end inject

end YM.Maxwell.Free
