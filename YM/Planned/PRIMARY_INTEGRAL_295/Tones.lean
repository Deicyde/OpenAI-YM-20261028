import YM.Next.ROTATIONS.Flat
import YM.Planned.PRIMARY_INTEGRAL_295.Columns
import YM.Work.B04


/-!
# Basis polynomial at changing block thresholds

Entire real ball jets for the unmasked canonical column on the stencil
only. No uniform paths on the growth envelope. Slot-pop and weight-pop
from the actual SectionData, no other direction identifications. The
constants here fixed before the step at the *unscaled* radius. Customer has
to actually meet that radius if used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Tones
open Function Filter Set Metric Labels Lattice Source RG Place
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {f : E → F} {n k l : ℕ}

-- ℝ smul (matches ℂ scaling on probe by the cast).
def coat (f : E → F) (l : ℕ) (t : ℝ) (x : E) : F := (t^l)⁻¹ • f (t • x)

lemma coat_smooth (h : ContDiff ℝ ω f) (l : ℕ) (t : ℝ) : ContDiff ℝ ω (coat f l t) :=
  contDiff_const.smul (h.comp (contDiff_const.smul contDiff_id))

lemma color_jet (h : ContDiff ℝ ω f) (l : ℕ) (t : ℝ) (x : E) (k : ℕ) :
    iteratedFDeriv ℝ k (coat f l t) x = (t^k/t^l) • iteratedFDeriv ℝ k f (t • x) := by
  let L : E →L[ℝ] E := t • ContinuousLinearMap.id ℝ E
  change iteratedFDeriv ℝ k ((t^l)⁻¹ • (f ∘ L)) x=_
  rw [iteratedFDeriv_const_smul_apply ((h.comp L.contDiff).contDiffAt.of_le le_top),
    L.iteratedFDeriv_comp_right h _ le_top]
  ext1 v
  change (t^l)⁻¹ • iteratedFDeriv ℝ k f (t • x) (fun i => t • v i)= _
  have he := (iteratedFDeriv ℝ k f (t • x)).map_smul_univ (fun _=> t) v
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at he
  rw [he,smul_smul, mul_comm (t^l)⁻¹, div_eq_mul_inv]; rfl

/-- Vanishing at 0 in real tensors; uniform order prices through k,
not depending on gauge tag, period, cutoffs or t. -/
lemma bodyPrice [ProperSpace E] (hf : ContDiff ℝ ω f) (h : ∀ j<l, iteratedFDeriv ℝ j f 0=0) (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ (t : ℝ) (x : E), t∈Ioc 0 1 → ‖t • x‖≤R →
      ‖iteratedFDeriv ℝ k (coat f l t) x‖ ≤ C*(1+‖x‖)^l := by
  let m := l-k
  have hh (j : ℕ) (_ : k≤j) (hj:j<k+m) : iteratedFDeriv ℝ j f 0=0 := h _ (by unfold m at hj; omega)
  obtain ⟨C,hC,H⟩ := Outer.earnings f (hf.of_le le_top) k m hh R
  refine ⟨C,hC,fun t x ht hx=>?_⟩
  have hy : t ≤ 1 := ht.2; have hv:t>0:=ht.1
  rw [color_jet hf _ _ _ k,norm_smul,Real.norm_of_nonneg (by positivity)]
  apply (mul_le_mul_of_nonneg_left (H _ hx) (by positivity)).trans
  rw [norm_smul,Real.norm_of_nonneg hv.le,mul_pow]
  have he : t^k/t^l*t^m ≤ 1 := by
    rw [div_mul_eq_mul_div,← pow_add]; exact (div_le_one (by positivity)).mpr
      (pow_le_pow_of_le_one hv.le hy (by unfold m; omega))
  have Hx : 1≤1+‖x‖ := by simp
  have hx' : ‖x‖^m≤(1+‖x‖)^l := (pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left zero_le_one) m).trans
    (pow_le_pow_right₀ Hx (by unfold m; omega))
  calc
    _ = C*(t^k/t^l*t^m*‖x‖^m) := by ring
    _ ≤ C*(1*(1+‖x‖)^l) := mul_le_mul_of_nonneg_left (mul_le_mul he hx' (by positivity) zero_le_one) hC
    _ = _ := by rw [one_mul]

/-- Keep explicit the norm of evaluation directions so that unbounded
normalized fluctuations may be integrated later. Doesn't assume logs exist. -/
def Width (f : E → F) (k l : ℕ) (R C : ℝ) : Prop :=
    0≤C ∧ ∀ j ≤ k, ∀ (t : ℝ) (x : E), t∈Ioc 0 1 → ‖t • x‖≤R → ‖iteratedFDeriv ℝ j (coat f l t) x‖ ≤ C*(1+‖x‖)^l

lemma on_body [ProperSpace E] (hf : ContDiff ℝ ω f) (h : ∀ j < l, iteratedFDeriv ℝ j f 0=0) (k : ℕ) (R : ℝ) :
    ∃ C:ℝ, Width f k l R C := by
  choose D hD H using fun n => bodyPrice hf h n R
  refine ⟨∑ n∈Finset.range (k+1),D n, Finset.sum_nonneg (fun i _=> hD i),fun n hn t x ht hx => (H n t x ht hx).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hD i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hn))) (by positivity)

lemma Width.diff (hf : ContDiff ℝ ω f) {R C : ℝ} (h : Width f k l R C) {j : ℕ} (hj : j < k)
    {x y : E} {t r : ℝ} (ht : t∈Ioc 0 1) (ha : ‖x‖≤r) (hb : ‖y‖≤r) (hx : ‖t • x‖≤R) (hy : ‖t • y‖≤R) :
    ‖iteratedFDeriv ℝ j (coat f l t) x - iteratedFDeriv ℝ j (coat f l t) y‖ ≤ C*(1+r)^l * ‖x-y‖ := by
  have he : 0<t := ht.1
  let u := min r (R/t)
  let f' := coat f l t
  have hh : ContDiff ℝ ω f' := coat_smooth hf _ _
  have hM (z : E) : z∈closedBall (0:E) u ↔ ‖z‖≤r ∧ ‖t • z‖≤R := by
    rw [mem_closedBall,dist_zero_right]; unfold u; rw [le_min_iff,le_div_iff₀ he,norm_smul,Real.norm_of_nonneg he.le,mul_comm]
  refine (convex_closedBall (0:E) u).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hh.differentiable_iteratedFDeriv (by simp) z) ?_ ((hM y).mpr ⟨hb,hy⟩) ((hM x).mpr ⟨ha,hx⟩)
  intro z hz
  rw [norm_fderiv_iteratedFDeriv]; apply (h.2 _ hj _ _ ht ((hM z).1 hz).2).trans
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (add_le_add_right ((hM z).1 hz).1 _) _) h.1
end

variable {G : Gauge} {n d : ℕ} {F : Labels.Frame G d}

abbrev tint (T : SectionData F) (i : F.Index) := coat (column T i) (F.grades i).2

lemma columnPrice (T : SectionData F) (h : Bid.pop T) (i : F.Index) (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, Width (column T i) k (F.grades i).2 R C := by
  haveI := FiniteDimensional.proper ℝ (Dev T.stencil G)
  exact on_body (column_smooth T i) (radials_vanish T h i) _ _

lemma columnCostLower (A : Source.Hol G) (T : SectionData F) (h : T.Sound A) (i : F.Index) (t : ℝ)
    (w : Fin n → ℕ) (hw : ∑ j,w j < (F.grades i).1) (u : Fin n → Potential G) (hu : ∀ j, u j∈rangeLt (Axis→G.Color) (w j)) :
    iteratedFDeriv ℝ n (tint T i t) 0 (fun j => ping T.stencil (u j))=0 := by
  unfold tint; rw [color_jet (column_smooth T i),smul_zero, smul_apply, lower A T h i w hw u hu,smul_zero]

end YM.Planned.PrimaryIntegral295.Tones
