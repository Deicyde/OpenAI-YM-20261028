import YM.Contacts.Normal.Pieces
import YM.Contacts.Normal.ShellTest
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Uniform angular subdivisions of a nonzero annulus

Off total collapse cover by patches guaranteeing separation for **all** subcenters that might be
used subsequently. Changing patches doesn't change the punctured distribution. Dyadic estimates
use a chosen subdivision with uniform clearance in units of that shell. It is for the proof and
may depend on the ambient space of tests. Compactness here is in normal coordinates, not whole
stages. A finite number of sectors (possibly disconnected; one family per partition).
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Normal
open Function Filter Set Metric MeasureTheory Submodule MultipleContact
open scoped Topology Classical ContDiff Manifold BigOperators InnerProductSpace
variable {k : ℕ} {g : Group k} {E : Type*} [NormedAddCommGroup E][InnerProductSpace ℝ E]
variable (P : E→ₗᵢ[ℝ] Points k)
lemma grouping_inside (Q : Pieces g)(x : Points k)(hx : Q= Finpartition.ofSetSetoid (Setoid.ker (fun i : Fin k=>x i)) g) (i : Q.parts) : Collapsed i.val x:= by
   apply (collapsed_iff ..).mpr; intro a ha b hb
   have he: b∈ Q.part a:= by rw [Q.part_eq_of_mem i.property ha]; exact hb
   rw [hx] at he; exact (Finpartition.mem_part_ofSetSetoid_iff_rel g|>.1 he).2.2
lemma separates_grouping (Q : Pieces g)(x : Points k)(hx : Q= Finpartition.ofSetSetoid (Setoid.ker (fun i : Fin k=>x i)) g) (i j : Q.parts)(hh : i≠ j)(a : (i:Group k))(b : (j:Group k)) : x a.val≠ x b.val := by
   intro h; apply hh; have he : b.val∈ Q.part a.val := by rw [congrArg (fun H:Pieces g=> H.part a.val) hx]; exact Finpartition.mem_part_ofSetSetoid_iff_rel g |>.2 ⟨Q.le i.property a.property,Q.le j.property b.property,h⟩

   rw [Q.part_eq_of_mem i.property a.property] at he; exact Subtype.ext (Q.eq_of_mem_parts i.property j.property he b.property)
variable [FiniteDimensional ℝ E]

abbrev Nails (i : Group k) := {p : Group k // p⊆i ∧ p.Nonempty}
/-- A strict split, with g still on a shell. Empty allowed. Membership is independent
of the g centroid, and uses no pairing with exteriors. -/
def bright (Q : Pieces g) : Set E:= {x|∀ i j:Q.parts, i≠j → ∀ (u:Nails i.val)(v:Nails j.val), centroid u.val (P x)≠centroid v.val (P x)}
-- IH needs lower bounds, extract from compact tsupport × annulus
abbrev Splittings (g : Group k) := { Q: Pieces g // Q≠⊤}
lemma equality_opens (x : Points k) {Q : Pieces g} (h : Q= Finpartition.ofSetSetoid (Setoid.ker (fun i=> x i)) g) {i j : Q.parts} (he : i≠j) (u : Nails i.val)(v : Nails j.val) : centroid u.val x ≠ centroid v.val x:= by
   obtain ⟨a,ha⟩:= u.property.2; obtain ⟨b,hb⟩:=v.property.2; have ha':=u.property.1 ha; have hb':=v.property.1 hb
   rw [centroid_same u.property.2 _ (x a) fun z hz=> (collapsed_iff ..).1 (grouping_inside Q x h i|>.subgroups u.property.1) _ hz _ ha, centroid_same v.property.2 _ (x b) fun z hz=> (collapsed_iff ..).1 (grouping_inside Q x h j |>.subgroups v.property.1) _ hz _ hb]; exact separates_grouping Q x h i j he ⟨a,ha'⟩ ⟨b,hb'⟩
omit [FiniteDimensional ℝ E] in
lemma open_bright (Q : Pieces g) : IsOpen (bright P Q):=by
    unfold bright; apply isOpen_iff_mem_nhds.mpr; intro x (hx : ∀ i j: _,_); change ∀ᶠ x:E in 𝓝 x,∀ (i j : Q.parts), i≠j → ∀ (u:Nails i.val) (v:Nails j.val),centroid u.val (P x)≠centroid v.val (P x); apply eventually_all.mpr
    intro i; apply eventually_all.mpr; intro j; by_cases h:i=j; subst j; simp
    have he(u:Nails i.val)(v:Nails j.val): ∀ᶠ y in 𝓝 x, centroid u.val (P y) ≠ centroid v.val (P y):=
       (isClosed_eq ((centroid _).continuous.comp P.continuous) ((centroid _).continuous.comp P.continuous)).isOpen_compl.mem_nhds (hx i j h u v)
    filter_upwards [ eventually_all.mpr fun u=> (eventually_all.mpr (he u)) ] with y hy; intro _; exact hy
lemma on_cover (hp : plane g ≤ LinearMap.range P.toLinearMap)(hg : g.Nonempty) : sun (normalOn P g) 1 ⊆ ⋃ q:Splittings g, bright P q.val := by
   intro x hx; let Q:= Finpartition.ofSetSetoid (Setoid.ker (fun i=> (P x) i)) g; refine mem_iUnion.mpr ⟨⟨Q,?_⟩,fun i j hh=> equality_opens _ rfl hh⟩ -- reduction? lambda dots
   intro h; have he:=one_set Q h hg; have hh:= grouping_inside Q (P x) rfl ⟨g,he.symm ▸ Finset.mem_singleton_self g⟩; have ht:=(show ‖(normalOn P g).starProjection x‖∈Icc ((1:ℝ)/2) (2*1) from hx).1; rw [(local_collapse hp x).mp hh,norm_zero] at ht; norm_num at ht

local notation "K!" => normalOn P g
private def base (P : E→ₗᵢ[ℝ] Points k) (g : Group k) := (normalOn P g).subtypeL ⁻¹' sun (normalOn P g) 1 -- notice macro unused
private lemma ring_compact (g : Group k) : IsCompact (base P g):=by
   have he:= (closed_sun (normalOn P g) 1).preimage (normalOn P g).subtypeL.continuous; apply (isCompact_closedBall (0:normalOn P g) 2).of_isClosed_subset he
   intro v hv; rw [mem_closedBall,dist_zero_right]; change ‖v.val‖≤ 2; have h: ‖(normalOn P g).starProjection v.val‖ ≤ 2*1:= hv|>.2; rwa [mul_one, starProjection_eq_self_iff.mpr v.property] at h
-- reference to g explicit in variable P g
structure Fans (P : E→ₗᵢ[ℝ] Points k) (g : Group k) where
    sector : Splittings g→ SmoothTests (normalOn P g)
    covers (x : normalOn P g)(hx : (x:E) ∈ sun (normalOn P g) 1) : ∑ i:Splittings g,(sector i).val x = 1
    sub (i : Splittings g)(x : normalOn P g)(hx : x ∈ tsupport (sector i).val) : (x:E)∈ bright P i.val

private def functorF (P': E→ₗᵢ[ℝ] Points k) (f : SmoothPartitionOfUnity (Splittings g) 𝓘(ℝ,(normalOn P' g)) (normalOn P' g) (base P' g)) (hf : f.IsSubordinate (fun q=> (normalOn P' g).subtypeL ⁻¹' bright P' q.val)) : Fans P' g where
      sector q:= ⟨fun x=> (f q x:ℂ), Complex.ofRealCLM.contDiff.comp (contMDiff_iff_contDiff.mp (f q).contMDiff)⟩
      covers x hx:= by simp only; rw [← Complex.ofReal_sum, f.sum_finsupport' _ (show x∈base P' g from hx) (Finset.subset_univ ..),Complex.ofReal_one]
      sub i x hx:= by
           have he:= show x∈ tsupport (fun x=>(f i x:ℂ)) from hx
           have hu : tsupport (fun x=>(f i x:ℂ)) ⊆ tsupport (f i):= closure_mono fun x h=>fun h'=> h ( (congrArg Complex.ofReal h').trans Complex.ofReal_zero)
           exact hf i (hu he)


lemma available_fans (hp : plane g ≤ LinearMap.range P.toLinearMap) (hg : g.Nonempty) : Nonempty (Fans P g):=by
   let K:= K!; let r (q:Splittings g):= K.subtypeL ⁻¹' bright P q.val; let s:=base P g
   have ht: s ⊆ ⋃ q, r q:= by rw [← preimage_iUnion]; exact preimage_mono (on_cover P hp hg)
   obtain ⟨f,hf⟩:= SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ,(K:Type _)) ((ring_compact P g).isClosed) r (fun i=> (open_bright P i.val).preimage K.subtypeL.continuous) ht -- syntax K:Type
   refine ⟨functorF P f hf⟩ -- implement `where` or inline

lemma margin (u : Fans P g) (Q : Splittings g) (i j : Q.val.parts)(h : i≠j) (a : Nails i.val)(b:Nails j.val) : ∃ c> (0:ℝ),∀ x:E,x∈ normalOn P g → x∈ sun (normalOn P g) 1 → -- avoid Dep proof
   (normalOn P g).orthogonalProjectionOnto x ∈ tsupport (u.sector Q).val → c ≤ ‖centroid a.val (P x)-centroid b.val (P x)‖:=by
   let L:= normalOn P g; let D:= base P g ∩ tsupport (u.sector Q).val; let f (x:L):= ‖centroid a.val (P x.val)-centroid b.val (P x.val)‖
   suffices he : ∃ c> (0:ℝ),∀ x∈ D,c≤ f x by
     obtain ⟨c,hc,h⟩:=he; refine ⟨c,hc,fun x hx hh hl=> h ⟨x,hx⟩ ⟨hh,?_⟩⟩; exact (show L.orthogonalProjectionOnto x=⟨x,hx⟩ from Subtype.ext (starProjection_eq_self_iff.mpr hx)) ▸ hl
   rcases D.eq_empty_or_nonempty with he|he; rw [he]; exact ⟨1,zero_lt_one,by simp⟩
   obtain ⟨x,hx,hL⟩:= ((ring_compact P g).inter_right (isClosed_tsupport ..)).exists_isMinOn he (Continuous.continuousOn (f:=f) (Continuous.norm (Continuous.sub ((centroid _).continuous.comp (P.continuous.comp continuous_subtype_val)) ((centroid _).continuous.comp (P.continuous.comp continuous_subtype_val)))))
   exact ⟨f x,norm_pos_iff.mpr (sub_ne_zero.mpr (u.sub Q x hx.2 i j h a b)),fun x'=> @hL x'⟩
end YM.Contacts.Normal
