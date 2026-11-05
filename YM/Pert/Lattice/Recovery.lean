import YM.Maxwell.Exterior
import YM.Pert.Lattice.Series
/-! Linear map from arrays of plaquette jets (even off continuum Bianchi shell) into radial Taylor labels of common weights. -/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Bare
open Function Maxwell Tensor Labels ContinuousMultilinearMap
open scoped Topology ContDiff
variable {G : Gauge} {j : ℕ}
abbrev Response (G : Gauge) (j : ℕ) := Axis → Axis → (Fin j → Axis) → G.Color

def spaceMon {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (γ : Fin j → Axis) (v : F) : T E4 F j :=
    ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin j) ℝ).compContinuousLinearMap fun i => compAxis (γ i)).smulRight v
lemma mon_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (γ : Fin j → Axis) (v : F) (x) :
    spaceMon γ v x = (∏ i, x i (γ i)) • v := rfl
def forms (a : Response G j) (i k : Axis) : T E4 G.Color j := ∑ γ, spaceMon γ ((1/2:ℝ) • (a i k γ - a k i γ))
lemma forms_swap (a : Response G j) (i k : Axis) : forms a i k = - forms a k i := by
  unfold forms; ext1 t; simp only [sum_apply,neg_apply,mon_eq,← Finset.sum_neg_distrib,← smul_neg,neg_sub]

/-- Contract antisymmetric derivative array against radial leg; this only projects
linear continuum jets, does not take the interacting theory modulo any equation. -/
def radialize (a : Response G j) : Taylor G j := ⟨fun i => ((↑(j+2 : ℕ)):ℝ)⁻¹ • ∑ k, added (forms a k i) (compAxis k),
  ⟨fun i r s => by simp only [smul_apply,sum_apply,added_sym _ _ r s], fun z => by
    have eq := forms_swap a
    simp only [diagonal, smul_apply, sum_apply]
    let t := ∑ i : Axis, z i • (((↑(j+2 : ℕ)):ℝ)⁻¹ • ∑ k, z k • diagonal (forms a k i) z)
    simp_rw [show ∀ i k, added (forms a k i) (compAxis k) (fun _ => z) = z k • diagonal (forms a k i) z from
      fun _ _ ↦ added_diag ..]
    change t = 0
    have H : t = - t := by
      dsimp only [t]
      simp_rw [Finset.smul_sum, ← Finset.sum_neg_distrib, ← smul_neg]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a' _; apply Finset.sum_congr rfl
      intro b _
      nth_rw 1 [eq a' b]
      simp only [smul_smul, diagonal, neg_apply]; congr 1; ring
    have he : (2:ℝ) • t = 0 := by rw [two_smul]; nth_rw 1 [H]; simp
    exact (smul_eq_zero.mp he).resolve_left (by norm_num)⟩⟩
lemma radial_value (a : Response G j) (i x) : (radialize a).value i x = ((↑(j+2 : ℕ)):ℝ)⁻¹ • ∑ k,
       x k • ∑ γ, (∏ u, x (γ u)) • ((1/2:ℝ) • (a k i γ-a i k γ)) := by
  have h : (radialize a).value i x = ((↑(j+2 : ℕ)):ℝ)⁻¹ • (∑ k, diagonal (added (forms a k i) (compAxis k)) x) := by
    unfold Taylor.value diagonal radialize; simp
  rw [h]; congr 1; refine Finset.sum_congr rfl (fun k _ => ?_); rw [added_diag]; change x k • (forms a k i (fun _ => x))=_
  rw [forms,sum_apply]; simp only [mon_eq]
def radialMap : Response G j →ₗ[ℝ] Taylor G j where
  toFun := radialize
  map_add' a b := Taylor.value_ext _ _ (funext (fun i => funext (fun x => by
    change _ = (radialize a).value i x + (radialize b).value i x
    simp [radial_value, Pi.add_apply, add_sub_add_comm, smul_add, Finset.sum_add_distrib])))
  map_smul' r a := Taylor.value_ext _ _ (funext (fun i => funext (fun x => by
    change _ = r • (radialize a).value i x
    simp [radial_value, Pi.smul_apply, ← smul_sub, smul_comm _ r, Finset.smul_sum])))
lemma radial_color (u : G.El) (a : Response G j) : radialize (fun i k γ => G.adjoint u (a i k γ)) = Taylor.paint u (radialize a) :=
  Taylor.value_ext _ _ (by funext i x; simp [Taylor.paint_value,radial_value])

def components (a : Taylor G j) : Response G j := fun i l r => Maxwell.takeCurl a i l (fun u => basis (r u))
lemma forms_components (a : Taylor G j) (i l : Axis) : forms (components a) i l = Maxwell.takeCurl a i l := by
  ext1 z
  let Q := Maxwell.takeCurl a i l
  rw [forms,sum_apply]
  have eq (γ : Fin j → Axis) : ((1/2:ℝ) • (components a i l γ - components a l i γ)) = components a i l γ := by
    unfold components; rw [(closedCurl a).antisymmetric l i, neg_apply,sub_neg_eq_add,← two_smul ℝ,smul_smul]; norm_num
  simp_rw [eq,mon_eq]
  have ht (v : E4) : ∑ i : Axis, v i • basis i = v := by
    ext1 i; simp [WithLp.ofLp_sum, Finset.sum_apply,PiLp.smul_apply,basis,Pi.single_apply, ite_mul, mul_ite, eq_comm]
  have he (i : Fin j) : ∑ l : Axis, z i l • basis l = z i := ht _
  conv_rhs => rw [← funext he]
  change _ = Q.toMultilinearMap _; rw [MultilinearMap.map_sum_finset]; simp_rw [Q.toMultilinearMap.map_smul_univ]; simp only [Fintype.piFinset_univ]; rfl
lemma complete (a : Taylor G j) : radialize (components a) = a := by
  have e : radialize (components a) = Maxwell.contracted (Maxwell.closedCurl a) := by
    apply Subtype.ext; funext i; change ((↑(j+2 : ℕ)):ℝ)⁻¹ • _ = _; simp only [forms_components]; rfl
  exact e.trans (Maxwell.potential_recover a)
end YM.Pert.Bare
