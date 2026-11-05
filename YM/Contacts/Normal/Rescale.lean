import YM.Contacts.Normal.Dimension
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! # Anisotropic scales on the ambient space

Parent integration estimates can assume the ambient space anisotropically scaled as long as
(active normal subspace) and (all directions orthogonal to it) are reduced by that scale map, and
the normal block reads the intended scalar size. The latter leaves the orthogonal coordinates
independent. This freedom makes it straightforward to pay the correct relative volume factors at
internal collision nodes.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule
open scoped ContDiff Topology Classical BigOperators InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable (K : Submodule ℝ E) {L : Submodule ℝ E} {r t s : ℝ}

/-- Scale along K only. At zero size, orthogonal projection away from K. -/
def slide (t : ℝ) : E →L[ℝ] E:= ContinuousLinearMap.id ℝ _ + (t-1) • K.starProjection
lemma slide_formula (t : ℝ) (x : E) : slide K t x = (x-K.starProjection x)+t • K.starProjection x := by
  simp only [slide,_root_.add_apply,ContinuousLinearMap.id_apply,_root_.smul_apply]; rw [sub_smul,one_smul]; abel
lemma foot (t : ℝ) (x : E) : slide K t x = t • K.starProjection x + Kᗮ.starProjection x:= by rw [slide_formula,add_comm,starProjection_orthogonal_val]
lemma slide_zero (x : E) : slide K 0 x=x-K.starProjection x:= by simp [slide_formula]
lemma slide_one (x : E) : slide K 1 x=x:= by simp [slide_formula]
lemma slip_mem (t : ℝ) {x : E} (h : x∈K) : slide K t x=t • x:= by rw [slide_formula,starProjection_eq_self_iff.mpr h,sub_self,zero_add]
lemma slip_hide (t : ℝ) {x : E} (h : x∈ Kᗮ) : slide K t x=x:= by rw [foot,K.starProjection_apply_eq_zero_iff.mpr h,smul_zero,starProjection_eq_self_iff.mpr h,zero_add]
lemma slip (t : ℝ) (x : E) : K.starProjection (slide K t x) = t • K.starProjection x:= by
  rw [foot,map_add,map_smul, starProjection_eq_self_iff.mpr (K.starProjection_apply_mem _), K.starProjection_apply_eq_zero_iff.mpr (Kᗮ.starProjection_apply_mem _),add_zero]
lemma slip_away (t : ℝ) (x : E) : slide K t x-K.starProjection (slide K t x)=x-K.starProjection x:= by rw [slip,slide_formula]; abel
lemma slip_inspect (t s : ℝ) (x : E) : slide K t (slide K s x)=slide K (t*s) x:= by rw [slide_formula,slip_away,slip,slide_formula,mul_smul]
lemma slide_smooth : ContDiff ℝ ∞ (fun p:E × ℝ=>slide K p.2 p.1) := by
  simp_rw [slide_formula]; apply (contDiff_fst.sub (K.starProjection.contDiff.comp contDiff_fst)).add
    (contDiff_snd.smul (K.starProjection.contDiff.comp contDiff_fst))

def resize (t : ℝ) (h : t ≠ 0) : E ≃L[ℝ] E where
  toFun := slide K t
  invFun := slide K t⁻¹
  left_inv := fun x=> by rw [slip_inspect, inv_mul_cancel₀ h, slide_one]
  right_inv := fun x=> by rw [slip_inspect,mul_inv_cancel₀ h,slide_one]
  continuous_toFun := ContinuousLinearMap.continuous _
  continuous_invFun := ContinuousLinearMap.continuous _
  map_add' := map_add _
  map_smul' := map_smul _
@[simp] lemma resizing (t) (h) (x : E) : resize K t h x=slide K t x:=rfl
@[simp] lemma return_size (t) (h) (x : E) : (resize K t h).symm x=slide K t⁻¹ x:=rfl
lemma slide_det (t : ℝ) : LinearMap.det (slide K t).toLinearMap = t^(Module.finrank ℝ K) := by
  let L:=K.prodEquivOfIsCompl _ K.isCompl_orthogonal
  let D:= LinearMap.prodMap (t • (LinearMap.id (R:=ℝ) (M:=K))) (LinearMap.id (R:=ℝ) (M:=Kᗮ)); have h : L.toLinearMap ∘ₗ (D ∘ₗ L.symm.toLinearMap) = (slide K t).toLinearMap:= by
    ext x; obtain ⟨⟨a,b⟩,rfl⟩:=L.surjective x; simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]; change ((t • a):K).val+b.val=slide K t (a.val+b.val); rw [map_add,slip_mem _ _ a.property,slip_hide _ _ b.property]; rfl
  rw [← h,LinearMap.det_conj]; unfold D; rw [LinearMap.det_prodMap,LinearMap.det_smul,LinearMap.det_id,LinearMap.det_id]; ring
lemma absorb_projection {K : Submodule ℝ E} (h : K ≤ L) (x : E) : K.starProjection (L.starProjection x) = K.starProjection x:= by
  have ht:= sub_starProjection_mem_orthogonal (K:=L) x; have he:= K.starProjection_apply_eq_zero_iff.mpr (Submodule.orthogonal_le h ht); rw [map_sub] at he; exact (sub_eq_zero.mp he).symm

/-- A is an allowed anisotropic dilation; scale t along K and don't bring the complementary
parameters into normal positions. -/
structure Proper (A : E ≃L[ℝ] E) (t : ℝ) (K : Submodule ℝ E) : Prop where
  normal x : K.starProjection (A x)= t • K.starProjection x
  acts x (h : x∈ K) : A x=t • x
namespace Proper
variable {K} {A : E≃L[ℝ] E} (h : Proper A t K)
include h
lemma commute (c : ℝ) (x : E) : A (slide K c x)=slide K c (A x):= by
  have hx:=h.acts _ (K.starProjection_apply_mem x)
  simp only [slide_formula,map_add,map_sub,map_smul]; rw [hx, h.normal x]
lemma before (x : E) : A (x-K.starProjection x)= A x-K.starProjection (A x):= by rw [← slide_zero, ← slide_zero, h.commute]
lemma acts_at (he : t≠0) {x:E} (hx : x∈ K) : A.symm x= t⁻¹ • x:= by apply A.injective; rw [map_smul,h.acts _ hx,inv_smul_smul₀ he,A.apply_symm_apply]
lemma within (he : L ≤ K) : Proper A t L:= by
   constructor; swap; · exact fun x hx=> h.acts x (he hx)
   intro x; rw [← absorb_projection he, h.normal,map_smul, absorb_projection he]
lemma grant (r : ℝ) (hr : r≠0) : Proper ((resize K r hr).trans A) (t*r) K := by
   constructor; · intro x; rw [ContinuousLinearEquiv.trans_apply,h.normal,resizing,slip,mul_smul]
   intro x hx; rw [ContinuousLinearEquiv.trans_apply,resizing,slip_mem _ _ hx,map_smul,h.acts _ hx,mul_comm,mul_smul]
lemma aside (r : ℝ) (hr : r≠0) (hg : K ≤ Lᗮ) : Proper ((resize L r hr).trans A) t K:= by
   constructor; · intro x; have hh : L ≤ Kᗮ := (Submodule.le_orthogonal_orthogonal _).trans (Submodule.orthogonal_le hg); rw [ContinuousLinearEquiv.trans_apply,h.normal]; change t • K.starProjection (x+(r-1) • L.starProjection x) = _; rw [map_add,map_smul,K.starProjection_apply_eq_zero_iff.mpr (hh (L.starProjection_apply_mem x)),smul_zero,add_zero]
   intro x hx; rw [ContinuousLinearEquiv.trans_apply,resizing,slip_hide _ _ (hg hx),h.acts _ hx]
lemma hands (c : ℝ) (hc:c≠0)(x : E) : ((resize K c hc).trans A) x = (A x - K.starProjection (A x)) + (t*c) • K.starProjection x := by
   rw [ContinuousLinearEquiv.trans_apply,resizing,h.commute,slide_formula,h.normal,mul_smul,smul_comm c t]
omit h in
lemma identity : Proper (ContinuousLinearEquiv.refl ℝ E) 1 K:= by constructor <;> intros <;> simp
end Proper
end YM.Contacts.Normal
