import YM.AnalyticNext.CUBIC_MATCH.Rays
import YM.AnalyticNext.CUBIC_MATCH.Region.Placement

set_option warningAsError false

/-!
# Permutations bought before origin moving

Total unnormalized read. Support calculations over shifts, with actual
ℝ color evaluated on link DOF. Make permutations a compatible average over
all tori before moving to relative displacements, preserving sup bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Filter Function Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {k : ℕ} {n : Side} {μ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {A : TapSet G k → E} {θ B : ℝ}

/-- Permute from old to new argument order. -/
def permuteTap (s : Equiv.Perm (Fin k)) : TapSet G k ≃ TapSet G k := Equiv.arrowCongr s (Equiv.refl (Tap G))
lemma perm_range (s : Equiv.Perm (Fin k)) (i : TapSet G k) : reachOf (permuteTap s i) = reachOf i := by
  unfold reachOf
  exact s.symm.sum_comp (fun j => size (i j).1)
lemma perm_verse (s : Equiv.Perm (Fin k)) (y : Site n) (i : TapSet G k) (a : Fin k → Dir G n) :
    verse y i (a ∘ s) = verse y (permuteTap s i) a := by
  unfold verse; refine Eq.trans ?_ (Equiv.prod_comp s (fun j => toneOf ((permuteTap s i) j) y (a j)))
  refine Finset.prod_congr rfl (fun j _ => ?_)
  change toneOf (i j) y (a (s j))=toneOf (i (s.symm (s j))) y (a (s j)); rw [s.symm_apply_apply]

omit [CompleteSpace E] in
lemma rotated_read (s : Equiv.Perm (Fin k)) (y : Site n) (a : Fin k → Dir G n) :
    receive A y (a ∘ s)=receive (A ∘ (permuteTap s).symm) y a := by
  let e := permuteTap (G:=G) s
  let P i := verse y i a • A (e.symm i)
  refine Eq.trans (tsum_congr (g:=fun i => P (e i)) fun i => ?_) (e.tsum_eq P)
  unfold P; rw [e.symm_apply_apply,← show verse y i (a ∘ s)=_ from perm_verse ..]

omit [CompleteSpace E] [NormedSpace ℝ E] in
lemma perm_budget (s : Equiv.Perm (Fin k)) (h : Decay reachOf θ B A) : Decay reachOf θ B (A ∘ (permuteTap s).symm) := by
  intro i; obtain ⟨j,rfl⟩ := (permuteTap s).surjective i; rw [perm_range]; simp only [Function.comp_apply,Equiv.symm_apply_apply]; exact h j

/-- same kernel for every torus. -/
def symTap (A : TapSet G k → E) (i : TapSet G k) :=
   (Fintype.card (Equiv.Perm (Fin k)):ℝ)⁻¹ • ∑ s : Equiv.Perm (Fin k), A ((permuteTap s).symm i)

omit [CompleteSpace E] in
lemma symTap_budget (h : Decay reachOf θ B A) : Decay reachOf θ B (symTap A) := by
  have ht : (Fintype.card (Equiv.Perm (Fin k)):ℝ) ≠ 0 := by positivity
  have he := (Decay.fin (s:=Finset.univ) fun s _ => perm_budget s h).scaled (Fintype.card (Equiv.Perm (Fin k)):ℝ)⁻¹
  simp only [Finset.sum_const,Finset.card_univ, nsmul_eq_mul,abs_of_nonneg (show 0 ≤ (Fintype.card (Equiv.Perm (Fin k)):ℝ)⁻¹ by positivity),
    inv_mul_cancel_left₀ ht] at he; exact he

lemma receive_sym (h : Decay reachOf θ B A) (he : 0 < θ) (y : Site n) (a : Fin k → Dir G n) : receive (symTap A) y a=
    (Fintype.card (Equiv.Perm (Fin k)):ℝ)⁻¹ • ∑ s : Equiv.Perm (Fin k), receive A y (a ∘ s) := by
  unfold receive symTap
  let r := (Fintype.card (Equiv.Perm (Fin k)):ℝ)⁻¹
  let H (s : Equiv.Perm (Fin k)) i := verse y i a • A ((permuteTap s).symm i)
  simp_rw [smul_comm (verse y _ a),Finset.smul_sum]
  rw [Summable.tsum_finsetSum (fun i _ => show Summable (fun j => r • H i j) from
    (receive_norm he (perm_budget i h) y a).of_norm.const_smul r)]
  refine Finset.sum_congr rfl fun i _ => ?_
  change ∑' j,r • H i j=r • receive A y (a ∘ i)
  rw [rotated_read,tsum_const_smul'']; rfl

def oneVerse (y : Site n) (u : TapSet G k) : Tensor.T (Dir G n) ℝ k := (ContinuousMultilinearMap.mkPiAlgebra ℝ _ ℝ).compContinuousLinearMap
  fun i => PiLp.proj 2 _ (u i).2.2 ∘L (ContinuousLinearMap.proj (wrap n (u i).1+y,(u i).2.1))



def tensorAt (A : TapSet G k → E) (y : Site n) : Tensor.T (Dir G n) E k := ∑' i,(oneVerse y i).smulRight (A i)

lemma tensorAt_read (h : Decay reachOf θ B A) (he : 0<θ) (y : Site n) (a : Fin k → Dir G n) :
    tensorAt A y a = receive A y a := by
  have hh i : ‖(oneVerse y i).smulRight (A i)‖ ≤ ‖A i‖ := by
    apply (ContinuousMultilinearMap.opNorm_le_iff (norm_nonneg (A i))).mpr
    intro m; change ‖verse y i m • A i‖ ≤ _
    rw [norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_left (verse_bounded y i m) (norm_nonneg _)
  have hx := Summable.of_norm_bounded (h.summable_norm (taps_decay _ he)) hh
  let e := ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Dir G n) E a
  exact e.map_tsum hx

/-- Given price on full diagonal test, obtain compatible the symmetric
Taylor coefficient (here OK any order) supported as a period-summed kernel. -/
theorem TotalRep.symmetry {c : μ → Side} {F : ∀ p, Dir G (c p) → E} (h : ∀ i, ContDiffAt ℝ k (F i) 0)
    (hp : TotalRep c k θ B (fun p x => term k (fun t : ℝ => F p (t • x)))) :
    ∃ A : TapSet G k → E, 0<θ ∧ 0 ≤ B ∧ Decay reachOf θ B A ∧
      ∀ p (a : Fin k → Dir G (c p)),∑ y,receive A y a=Tensor.coeff (F p) k 0 a := by
  obtain ⟨f,⟨he,hB,A,hA,H⟩,hh⟩ := hp
  refine ⟨symTap A,he,hB,symTap_budget hA,fun p a => ?_⟩
  let R : T (Dir G (c p)) E k := ∑ i : Site (c p), tensorAt A i
  have hq : symmetrize R=coeff (F p) k 0 := by
    refine ext_diag _ _ (symmetrize_sym _) (coeff_symm (h p)) (funext fun i => ?_)
    rw [symmetrize_diagonal,← term_ray (h p)]
    unfold diagonal R; simp_rw [sum_apply, tensorAt_read hA he, ← H]
    exact (hh ..).symm
  rw [← hq]
  simp only [receive_sym hA he,symmetrize,R,smul_apply,sum_apply,ContinuousMultilinearMap.domDomCongr_apply,Finset.smul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  exact Finset.sum_congr rfl fun j _ => congr_arg _ (tensorAt_read hA he j (a ∘ i)).symm
end YM.CubicMatch
