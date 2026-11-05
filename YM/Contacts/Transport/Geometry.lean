import YM.Contacts.Transport.Stream
import YM.Space.Orthogonal
import YM.Contacts.Normal.Rescale
/-! # Normal positions transported through multiple open-slot injections

Relativizes any ambient-patch formula to the arity in use. Coordinates may be isometrically
embedded into a joint stage with more slots, or changed by translation or a rotation of this
frame. Even when the dimensions allow for extra parameters, Jacobi coordinates computed in the
large stage on the *active* groups of slots are those of the smaller stage, not new normal choices.
Use about any (orthogonal) coincident placement of the normal roots & verify directly from matching
the locations of the slots in an aperture. Doesn't require relation between other slots. Could for
instance be comparing a transformed frame occupying a new set of exterior placements.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Transport
open Function Set Normal Submodule
open scoped Classical InnerProductSpace
variable {E F : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F]
variable {k n : ℕ}{U:E→ₗᵢ[ℝ] F}{P : E→ₗᵢ[ℝ] Points k}{T : F→ₗᵢ[ℝ] Points n}
 {f g : Normal.Group k}{t:Fin k↪ Fin n}{o:Points k}{o' : Points n}{c:F}{s : Ortho}{w : E4}
structure Ribbon (t : Fin k↪Fin n)(P:E→ₗᵢ[ℝ] Points k)(T:F→ₗᵢ[ℝ] Points n)(U:E→ₗᵢ[ℝ] F)(c:F)
    (o:Points k)(o':Points n) (s:Ortho) (w:E4)(g : Normal.Group k): Prop where
   full : plane g ≤ LinearMap.range P.toLinearMap
   full' : plane (current t g) ≤ LinearMap.range T.toLinearMap
   aligned : Collapsed g o
   aligned' : Collapsed (current t g) o'
   lie i : i∈g→∀ x, (T (U x+c)+o') (t i)=Ortho.motion s ((P x+o) i)+w
namespace Ribbon
variable (R : Ribbon t P T U c o o' s w g)
include R
local notation "K!" => normalOn P g
local notation "V" => current t g
local notation "K'" => normalOn T (current t g)
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma smaller (h : f⊆ g) : Ribbon t P T U c o o' s w f:= by
   have ht: current t f⊆ V:= Finset.map_subset_map.mpr h; exact ⟨(plane_le h).trans R.full,(plane_le ht).trans R.full',R.aligned.subgroups h,R.aligned'.subgroups ht,fun i hi=> R.lie _ (h hi)⟩
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma vector_move (i:Fin k) (hi:i∈g) (x:E) : T (U x) (t i)= Ortho.motion s ((P x) i):= by
   have hx:= R.lie _ hi x; have hz:=R.lie _ hi 0; simp only [map_add,map_zero,zero_add,PiLp.add_apply] at hx hz; linear_combination (norm := abel) hx-hz
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma slides_between (x:E)(_h : g.Nonempty) : centroid V (T (U x))=Ortho.motion s (centroid g (P x)):= by rw [centroid_formula,centroid_formula,carries,Finset.card_map, Finset.sum_map,map_smul,map_sum]; apply congr_arg; exact Finset.sum_congr rfl fun i hi=> R.vector_move _ hi x
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
lemma centroid_move (x:E) (hg:g.Nonempty) : centroid (current t g) (T (U x+c)+o')= Ortho.motion s (centroid g (P x+o))+w:= by
   rw [centroid_formula,centroid_formula,carries, Finset.sum_map, Finset.card_map, Finset.sum_congr rfl (g:=fun i=> Ortho.motion s ((P x+o) i)+w) (fun i hi=> R.lie _ hi x), Finset.sum_add_distrib,map_smul,map_sum,Finset.sum_const,←Nat.cast_smul_eq_nsmul ℝ,smul_add, inv_smul_smul₀]; exact_mod_cast hg.card_pos.ne'
omit [FiniteDimensional ℝ E] in
lemma c_tangent (_h : g.Nonempty) : (K').starProjection c=0:=by
   apply (local_collapse R.full' c).1; apply (collapsed_iff ..).2; rintro i hi j hj; obtain ⟨i,hi',rfl⟩:= Finset.mem_map.mp hi; obtain ⟨j,hj',rfl⟩:= Finset.mem_map.mp hj
   have hh(i:Fin k)(hi:i∈g): T c (t i)=(Ortho.motion s (centroid g o)+w) - centroid V o':=by
        have hv:= R.lie i hi 0; simp only [map_zero,zero_add,PiLp.add_apply,R.aligned i hi, R.aligned' _ (Finset.mem_map_of_mem _ hi)] at hv; rw [← hv,add_sub_cancel_right]
   rw [hh i hi',hh j hj']
-- norm equality by transporting full relative normals in E & F.
lemma relative (x:E)(hg:g.Nonempty) {i:Fin k}(hi:i∈g) : T ((K').starProjection (U x)) (t i)= Ortho.motion s (P ((K!).starProjection x) i):=by
   rw [localProjection R.full', radial_star,localProjection R.full,radial_star]; unfold radial; simp only [points_apply, if_pos hi, if_pos (show t i∈ V from Finset.mem_map_of_mem t hi), R.slides_between x hg, R.vector_move i hi x,map_sub]
lemma radiant (x:E)(h:g.Nonempty): ‖(K').starProjection (U x)‖ = ‖(K!).starProjection x‖:= by
   let y:=(K!).starProjection x; let Y:= (K').starProjection (U x); suffices hv: ⟪Y,Y⟫_ℝ=⟪y,y⟫_ℝ by
      simp_rw [real_inner_self_eq_norm_sq] at hv; nlinarith only [hv,norm_nonneg Y,norm_nonneg y]
   rw [← T.inner_map_map,← P.inner_map_map,PiLp.inner_apply,PiLp.inner_apply];
   have hp:∑ i∈g,⟪P y i,P y i⟫_ℝ= ∑ i,⟪P y i,P y i⟫_ℝ:= by apply Finset.sum_subset (Finset.subset_univ _); intro i _ hi; rw [(plane_iff.mp (show P y∈plane g from (normalOn P g).starProjection_apply_mem x)).2 i hi,inner_zero_left]
   have ht: ∑ i∈ V,⟪T Y i,T Y i⟫_ℝ=∑ i,⟪T Y i,T Y i⟫_ℝ:= by apply Finset.sum_subset (Finset.subset_univ _); intro i _ hi; rw [(plane_iff.mp (show T Y∈plane V from (K').starProjection_apply_mem (U x))).2 i hi,inner_zero_left]
   rw [← ht,← hp, carries, Finset.sum_map]; exact Finset.sum_congr rfl fun i hi=> by change ⟪_,_⟫_ℝ=_; simp_rw [Y,y,R.relative x h hi]; exact LinearIsometryEquiv.inner_map_map .. 
lemma embraces (hg : g.Nonempty) {x:E}(hx:x∈ K!) : U x∈ K' := ((K').mem_iff_norm_starProjection (U x)).mpr (by rw [radiant R x hg,Submodule.starProjection_eq_self_iff.mpr hx,U.norm_map])
lemma flow_normal (x:E)(hg:g.Nonempty): (K').starProjection (U x) = U ((K!).starProjection x) := by
    let y:= x-(K!).starProjection x; let Y:= (K!).starProjection x; have htt : (K!).starProjection y=0 := (K!).starProjection_apply_eq_zero_iff.mpr (sub_starProjection_mem_orthogonal x); have he:=R.radiant y hg; rw [htt,norm_zero] at he
    rw [show U x= U y+ U Y from by rw [← map_add,sub_add_cancel x Y], map_add,norm_eq_zero.mp he,zero_add,Submodule.starProjection_eq_self_iff.mpr (R.embraces hg ((K!).starProjection_apply_mem _))]
lemma shaded (x:E)(hg:g.Nonempty): (K').starProjection (U x+c)=U ((K!).starProjection x):= by rw [map_add,R.flow_normal x hg,R.c_tangent hg,add_zero]
lemma retreat (x:E)(u:ℝ)(hg:g.Nonempty) : U (slide K! u x)+c= slide K' u (U x+c):= by rw [slide_formula,slide_formula,R.shaded x hg,map_add,map_sub,map_smul]; abel
end Ribbon
end YM.Contacts.Transport
