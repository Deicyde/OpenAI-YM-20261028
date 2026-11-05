import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Layers
import YM.Push.PRICE_COMPILER.Authors



set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Finite-order calculus for log charts of actual paths

In particular, the first nonzero degree n=4 of a scalar correction is invariant under
use of another reconstruction of the coordinates with the identity Taylor degree 1.
**Analytic** germs throughout; no use of equality in all degrees to say two functions
agree globally. Can also use these tools for other Wilson uses (including at each fixed
L); this file only starts at the top.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Function Lattice RG RG.Supply Wilson Precision Exterior
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff

section Tools
variable {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f g : E → F} {u : H → E} {n : ℕ}

/-- All jets through n, anchored at zero. -/
structure UpTo (n : ℕ) (f g : E → F) : Prop where
  left : ContDiffAt ℝ ω f 0
  right : ContDiffAt ℝ ω g 0
  jets : ∀ j ≤ n, iteratedFDeriv ℝ j f 0=iteratedFDeriv ℝ j g 0

lemma UpTo.refl (h : ContDiffAt ℝ ω f 0) (n : ℕ) : UpTo n f f := ⟨h,h,fun _ _ => rfl⟩
lemma UpTo.trans {f' : E → F} (h : UpTo n f g) (h' : UpTo n g f') : UpTo n f f' :=
    ⟨h.left,h'.right,fun j hj => (h.jets j hj).trans (h'.jets j hj)⟩
omit [NormedAddCommGroup H] [NormedSpace ℝ H] in
lemma UpTo.average {s : Finset H} {a b : H → E → F} (h : ∀ i ∈ s,UpTo n (a i) (b i)) :
    UpTo n (fun x => ∑ i ∈ s, a i x) (fun x => ∑ i ∈ s, b i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp; exact UpTo.refl contDiffAt_const n
  | @insert i s hi ih =>
    have hc := h i (by simp)
    have ht := ih fun j hj => h _ (by simp [hj])
    simp only [Finset.sum_insert hi]
    refine ⟨hc.left.add ht.left,hc.right.add ht.right,fun j hj => ?_⟩
    rw [fun_iteratedFDeriv_add_apply (hc.left.of_le le_top) (ht.left.of_le le_top),
      fun_iteratedFDeriv_add_apply (hc.right.of_le le_top) (ht.right.of_le le_top),hc.jets j hj,ht.jets j hj]
-- interface drop norm assumptions on H
lemma UpTo.weight (h : UpTo n f g) (c : ℝ) : UpTo n (c • f) (c • g) :=
  ⟨h.left.const_smul c,h.right.const_smul c,fun j hj => by
    rw [iteratedFDeriv_const_smul_apply (h.left.of_le le_top),iteratedFDeriv_const_smul_apply (h.right.of_le le_top),h.jets j hj]⟩
lemma UpTo.add {l m : E → F} (h : UpTo n f g) (k : UpTo n l m) : UpTo n (f+l) (g+m) :=
  ⟨h.left.add k.left,h.right.add k.right,fun j hj => by
    rw [iteratedFDeriv_add_apply (h.left.of_le le_top) (k.left.of_le le_top),
      iteratedFDeriv_add_apply (h.right.of_le le_top) (k.right.of_le le_top),h.jets j hj,k.jets j hj]⟩
lemma UpTo.coeff (h : UpTo n f g) {j : ℕ} (he : j ≤ n) : ftaylorSeries ℝ f 0 j = ftaylorSeries ℝ g 0 j := h.jets j he

lemma UpTo.comp (h : UpTo n f g) (hu : ContDiffAt ℝ ω u 0) (hx : u 0=0) : UpTo n (f ∘ u) (g ∘ u) := by
  have hf : ContDiffAt ℝ ω f (u 0) := hx.symm ▸ h.left
  have hg : ContDiffAt ℝ ω g (u 0) := hx.symm ▸ h.right
  refine ⟨hf.comp _ hu,hg.comp _ hu,fun j hj => ?_⟩
  rw [iteratedFDeriv_comp hf hu le_top,iteratedFDeriv_comp hg hu le_top,hx]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition; rw [h.coeff (c.length_le.trans hj)]

/-- If an `OrderedFinpartition m` has length m (maximal), each part size is forced.
Thus the top term in Faa di Bruno for a degree-4 leading germ cannot see second/higher
derivatives of an inner coordinate map, even without fixing lower coefficients of that map.
-/
lemma Degree.sizes {j : ℕ} (c : OrderedFinpartition j) (he : j ≤ c.length) (i : Fin c.length) : c.partSize i=1 := by
  have hb : ∑ j : Fin c.length, c.partSize j = j := by
    have h := Fintype.card_congr c.equivSigma
    simpa [Fintype.card_sigma] using h
  have he (k : Fin c.length) : 1 ≤ c.partSize k := c.partSize_pos k
  by_contra hv
  have hn : (∑ _k : Fin c.length,(1:ℕ)) < ∑ k : Fin c.length,c.partSize k :=
    Finset.sum_lt_sum (fun k _ => he k) ⟨i,Finset.mem_univ i,(he i).lt_of_ne' hv⟩
  rw [hb] at hn; simp at hn; omega

/-- Compose two germs by maps with same tangent. Need f to start at degree n.
Avoid approximation on a torus: these are actual derivatives at origin. -/
lemma UpTo.valuation_comp {t : H → E} (hf : ContDiffAt ℝ ω f 0)
    (hz : ∀ j < n, iteratedFDeriv ℝ j f 0 = 0) (h : UpTo 1 u t) (hu : u 0=0) (ht : t 0=0) :
    UpTo n (f ∘ u) (f ∘ t) := by
  have ha : ContDiffAt ℝ ω f (u 0) := hu.symm ▸ hf
  have hb : ContDiffAt ℝ ω f (t 0) := ht.symm ▸ hf
  refine ⟨ha.comp _ h.left, hb.comp _ h.right, fun j hj => ?_⟩
  rw [iteratedFDeriv_comp ha h.left le_top, iteratedFDeriv_comp hb h.right le_top, hu,ht]
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl; intro c _
  by_cases he : c.length < n
  · ext1 v
    simp_rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,show ftaylorSeries ℝ f 0 c.length=0 from hz c.length he]; rfl
  have hh (i : Fin c.length) : ftaylorSeries ℝ u 0 (c.partSize i)=ftaylorSeries ℝ t 0 (c.partSize i) := by
    rw [Degree.sizes c (by omega)]; exact h.coeff le_rfl
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition; simp_rw [hh]

/-- Tensor Taylor form at order four. -/
def fourth (f : E → F) : E [×4]→L[ℝ] F := (24:ℝ)⁻¹ • iteratedFDeriv ℝ 4 f 0
def homog (f : E [×n]→L[ℝ] F) (x : E) := f fun _ => x
lemma contDiff_homog (f : E [×n]→L[ℝ] F) : ContDiff ℝ ω (homog f) := f.contDiff.comp (contDiff_pi.mpr fun _ => contDiff_id)
lemma homog_smul (f : E [×n]→L[ℝ] F) (c : ℝ) (x : E) : homog f (c • x)=c^n • homog f x := by
  unfold homog; rw [f.map_smul_univ (fun _ => c) (fun _ => x)]; simp

/-- Vanishing jet orders by exact scaling; also at n=0 (no requests). -/
lemma homog_lower (f : E [×n]→L[ℝ] F) (j : ℕ) (h : j < n) : iteratedFDeriv ℝ j (homog f) 0=0 := by
  let c := (2:ℝ); let g : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E
  have hg (x : E) : g x = c • x := rfl
  have he : homog f ∘ g = c^n • homog f := funext fun x => homog_smul f c x
  have hx : iteratedFDeriv ℝ j (homog f ∘ g) 0= c^n • iteratedFDeriv ℝ j (homog f) 0 := by
    rw [he,iteratedFDeriv_const_smul_apply ((contDiff_homog f).contDiffAt.of_le le_top)]
  ext1 v
  let P := iteratedFDeriv ℝ j (homog f) 0
  rw [g.iteratedFDeriv_comp_right (contDiff_homog _) _ le_top, g.map_zero] at hx
  have ht := DFunLike.congr_fun hx v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply] at ht
  simp_rw [hg] at ht
  rw [P.map_smul_univ (fun _ => c) v, smul_apply] at ht
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at ht
  have hz : (c^n-c^j) • P v=0 := by rw [sub_smul]; exact sub_eq_zero.mpr ht.symm
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos_of_lt (pow_lt_pow_right₀ (by norm_num [c]) h)))

/-- Actual contour-free fourth Taylor equality. Need symmetry of the target derivative;
have it for the analytic germs actually used. -/
lemma fourth_jet (h : ContDiffAt ℝ ω f 0) : iteratedFDeriv ℝ 4 (homog (fourth f)) 0 = iteratedFDeriv ℝ 4 f 0 := by
  ext1 v
  unfold homog
  rw [ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  have he (c : Equiv.Perm (Fin 4)) : fourth f (fun i => v (c i)) = (24:ℝ)⁻¹ • iteratedFDeriv ℝ 4 f 0 v := by
    unfold fourth; rw [smul_apply]; exact congrArg (_ • ·) (h.iteratedFDeriv_comp_perm _ _)
  simp_rw [he]
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_perm,Fintype.card_fin,show Nat.factorial 4=24 by decide,
    ← Nat.cast_smul_eq_nsmul ℝ,smul_smul]; norm_num

lemma fourth_restores (h : ContDiffAt ℝ ω f 0) (hz : ∀ j < 4, iteratedFDeriv ℝ j f 0=0) :
    UpTo 4 f (homog (fourth f)) := by
  refine ⟨h,(contDiff_homog _).contDiffAt,fun j hj => ?_⟩
  rcases lt_or_eq_of_le hj with h'|rfl
  · rw [hz _ h',homog_lower _ _ h']
  exact (fourth_jet h).symm
end Tools
end YM.UVNext.PricedKernels
