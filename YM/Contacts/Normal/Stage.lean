import YM.Space.Configurations
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Partition.Finpartition

/-! # Ambient spaces for the relative coordinate integrations

Many locations in a word. A block can collapse or separate without moving its centroid. Use
**orthogonal** normal coordinates throughout, not the rooted leaf-to-leaf ones. This uses all
positions to define an orthogonal complement to the coincidence plane, and `normalOn` is just
keeping these coordinates in an ambient plane (used when keeping parameters such as the top
centroid/exteriors fixed; take offsets also in the coincidence plane then). Pairings use Lebesgue
measure on these linear normal coordinates. No particular ordering of slots or arbitrary
choice of pivot is imposed by the prescription.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Finset MeasureTheory Submodule
open scoped Topology Classical BigOperators InnerProductSpace
variable {k : ℕ}
abbrev Group (k : ℕ) := Finset (Fin k)
variable {g f l : Group k} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : E →ₗᵢ[ℝ] Points k)
abbrev stage (k : ℕ) := Points k

def position (i : Fin k) : Points k →L[ℝ] E4 := LinearMap.toContinuousLinearMap (LinearMap.proj i ∘ₗ (PiLp.continuousLinearEquiv 2 ℝ _).toLinearMap)
lemma at_slot (x : Points k) (i : Fin k) : position i x = x i:=rfl
/-- Physical centroid. -/
def centroid (g : Group k) : Points k →L[ℝ] E4 := (g.card:ℝ)⁻¹ • ∑ i∈g,position i
lemma centroid_formula (g : Group k) (x : Points k) : centroid g x=(g.card:ℝ)⁻¹ • ∑ i∈g,x i := by
  simp [centroid,at_slot]
lemma centroid_same (hg : g.Nonempty) (x : Points k) (y : E4) (h : ∀ i∈g,x i=y) : centroid g x=y := by
  rw [centroid_formula,Finset.sum_congr rfl h,Finset.sum_const]; rw [← Nat.cast_smul_eq_nsmul ℝ, inv_smul_smul₀]; exact_mod_cast hg.card_pos.ne'
@[simp] lemma centroid_single (x : Points k) (i : Fin k) : centroid {i} x=x i:= centroid_same (Finset.singleton_nonempty _) _ _ (by simp)

/-- Configurations in the whole stage with the block all collapsed. Include the block centroid. -/
def Collapsed (g : Group k) (x : Points k) : Prop := ∀ i∈g, x i=centroid g x
lemma collapsed_iff (g : Group k) (x : Points k) : Collapsed g x ↔ ∀ i∈g,∀ j∈g, x i=x j := by
  refine ⟨fun h i hi j hj=> (h i hi).trans (h j hj).symm, fun h i hi=> (centroid_same ⟨i,hi⟩ _ _ (fun j hj=>h j hj i hi)).symm⟩
lemma Collapsed.subgroups {x : Points k} (h : Collapsed g x) (hu : f ⊆ g) : Collapsed f x := (collapsed_iff ..).mpr
  fun i hi j hj=> (h i (hu hi)).trans (h j (hu hj)).symm

/-- Full normal directions. -/
def plane (g : Group k) : Submodule ℝ (Points k) where
  carrier := {x | centroid g x=0 ∧ ∀ i∉g,x i=0}
  add_mem' {x y} hx hy := ⟨(map_add (centroid g) x y).trans (by rw [hx.1,hy.1,zero_add]),fun i hi=> show x i+y i=0 by rw [hx.2 i hi,hy.2 i hi,zero_add]⟩
  zero_mem' := ⟨map_zero _,fun _ _=>rfl⟩
  smul_mem' c x hx:= ⟨by rw [map_smul, hx.1,smul_zero], fun i hi=> show c • x i=0 by rw [hx.2 i hi, smul_zero]⟩
lemma plane_iff {x : Points k} : x∈plane g ↔ (∑ i∈g,x i)=0 ∧ ∀ i∉g,x i=0 := by
  change centroid g x=0 ∧ _ ↔ _; rw [centroid_formula]; rcases Finset.eq_empty_or_nonempty g with h|h
  · simp [h]
  simp [show (g.card:ℝ)≠0 by exact_mod_cast h.card_pos.ne']

lemma plane_le (h : g ⊆ f) : plane g ≤ plane f:= by
  intro p hp; obtain ⟨hr,hy⟩:= plane_iff.mp hp; exact plane_iff.mpr ⟨(Finset.sum_subset h (fun _ _=>hy _)).symm.trans hr,fun i hi=>hy i (mt (fun hi=>h hi) hi)⟩
lemma disjoint_orthogonal (h : Disjoint f g) : plane f ≤ (plane g)ᗮ := by
  intro x hx y hy; change ⟪y,x⟫_ℝ=0; rw [PiLp.inner_apply]; refine Finset.sum_eq_zero fun i hi=>?_; by_cases he:i∈f
  · rw [(plane_iff.mp hy).2 i (fun he'=> Finset.disjoint_left.mp h he he'),inner_zero_left]
  rw [(plane_iff.mp hx).2 i he,inner_zero_right]
def normalOn (g : Group k) : Submodule ℝ E := (plane g).comap P.toLinearMap
lemma on_plane (g : Group k){x : E} : x∈normalOn P g ↔ (P x)∈plane g:= Iff.rfl
lemma normal_le (h : g⊆f) : normalOn P g ≤ normalOn P f:= Submodule.comap_mono (plane_le h)
lemma normals_distinct (h : Disjoint f g) : normalOn P f ≤ (normalOn P g)ᗮ:= by
  intro x hx y hy; change ⟪y,x⟫_ℝ=0; rw [← P.inner_map_map]; exact disjoint_orthogonal h hx (P y) hy

/-- Project using centroid coordinates, keep other slots unchanged in subtracting the normal. -/
def radial (g : Group k) (x : Points k) : Points k := points (fun i=> if i∈g then x i-centroid g x else 0)
lemma radial_mem (g : Group k) (x : Points k) : radial g x ∈ plane g:= by
  apply plane_iff.mpr; refine ⟨?_,fun i hi=>by simp [radial,hi]⟩
  rcases Finset.eq_empty_or_nonempty g with h|h; simp [h]
  rw [show ∑ i∈g, radial g x i= ∑ i∈g,(x i-centroid g x) from Finset.sum_congr rfl fun i hi=>by simp [radial,hi], Finset.sum_sub_distrib, Finset.sum_const, centroid_formula]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_inv_smul₀,sub_self]; exact_mod_cast h.card_pos.ne'
lemma radial_star (g : Group k) (x : Points k) : (plane g).starProjection x= radial g x := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (radial_mem ..); intro y hy; rw [PiLp.inner_apply]
  rw [← Finset.sum_subset (Finset.subset_univ g) (fun i _ hi=> ?_)]
  · rw [Finset.sum_congr rfl (g:= fun i=> ⟪centroid g x,y i⟫_ℝ) (fun i hi=>?_), ← inner_sum, (plane_iff.mp hy).1,inner_zero_right]
    change ⟪x i-radial g x i,y i⟫_ℝ=_; simp [radial,hi]
  rw [(plane_iff.mp hy).2 i hi,inner_zero_right]
lemma collapsed_proj (x : Points k) : Collapsed g x ↔ (plane g).starProjection x=0 := by
  rw [radial_star]; refine ⟨fun h=>?_,fun h i hi=>?_⟩
  · refine PiLp.ext fun i=> ?_; by_cases hi:i∈g; rw [show radial g x i=x i-centroid g x from if_pos hi,h i hi,sub_self]; rfl
    exact if_neg hi
  apply sub_eq_zero.mp; rw [← show radial g x i=x i-centroid g x from if_pos hi, h]; rfl
lemma collapsed_orthogonal (g : Group k) (x : Points k) : Collapsed g x ↔ x∈ (plane g)ᗮ := (collapsed_proj x).trans ((plane g).starProjection_apply_eq_zero_iff)
lemma sub_radial {g : Group k} {x : Points k} {i : Fin k} (hi : i∈g) : (x-radial g x) i=centroid g x:= show x i-radial g x i=_ by rw [show radial g x i=x i-_ from if_pos hi,sub_sub_cancel]
variable {P} (h : plane g ≤ LinearMap.range P.toLinearMap) [FiniteDimensional ℝ E]
include h
lemma localProjection (x : E) : (P ((normalOn P g).starProjection x)) = (plane g).starProjection (P x) := by
  obtain ⟨v,(hv : P v = _)⟩:= h ((plane g).starProjection_apply_mem (P x))
  suffices eq:(normalOn P g).starProjection x=v by rw [eq,hv]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [on_plane,hv]; exact (plane g).starProjection_apply_mem _
  intro w hw; rw [← P.inner_map_map,map_sub,hv]; exact Submodule.starProjection_inner_eq_zero (P x) (P w) hw
lemma local_collapse (x : E) : Collapsed g (P x) ↔ (normalOn P g).starProjection x=0 := by
  rw [← P.injective.eq_iff,localProjection h,map_zero]; exact collapsed_proj _ -- lemma name
lemma local_centre (x : E) (i : Fin k) (hi : i∈g) : (P (x-(normalOn P g).starProjection x)) i=centroid g (P x) := by rw [map_sub,localProjection h,radial_star]; exact sub_radial hi
omit h in
lemma local_outside (x : E) (i : Fin k) (hi : i∉g) : (P (x-(normalOn P g).starProjection x)) i=(P x) i := by
  let y:= (normalOn P g).starProjection x; have ht: y∈normalOn P g:= (normalOn P g).starProjection_apply_mem x; have he:= (plane_iff.mp ((on_plane ..).mp ht)).2 i hi; rw [map_sub]; change (P x) i-(P y) i=_; rw [he, sub_zero]
lemma subgroup_from_center (x : E) (hg : f ⊆ g) (hf : f.Nonempty) : centroid f (P x)-centroid g (P x)=centroid f (P ((normalOn P g).starProjection x)):= by
  have he:= centroid_same hf (P (x-(normalOn P g).starProjection x)) _ (fun i hi=>local_centre h x _ (hg hi)); rw [← he, map_sub,map_sub,sub_sub_cancel]
lemma cohort_bounds (x : E) (hg : f⊆g) (hf : f.Nonempty) : ‖centroid f (P x)-centroid g (P x)‖ ≤ ‖(normalOn P g).starProjection x‖:= by
  rw [subgroup_from_center h x hg hf]; let v:=(normalOn P g).starProjection x
  have hm(i:Fin k):‖P v i‖ ≤ ‖v‖:= (PiLp.norm_apply_le (P v) i).trans_eq (P.norm_map v)
  have hh:0<(f.card:ℝ):=by exact_mod_cast hf.card_pos
  rw [centroid_formula, norm_smul,Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  apply (mul_le_mul_of_nonneg_left (norm_sum_le ..) (inv_nonneg.mpr hh.le)).trans; refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=> hm i)) (inv_nonneg.mpr hh.le)).trans ?_; rw [Finset.sum_const,nsmul_eq_mul, inv_mul_cancel_left₀ hh.ne']
end YM.Contacts.Normal
