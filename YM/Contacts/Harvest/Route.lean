import YM.Contacts.Normal.Bounded
/-!
# Compact geometry in an ambient space during shell recursion

Designed for uniform statements about shrinking *or* fixed subtraction length within
allowed apertures in Devices. Parameter type for lists of configurations/polygons on which
uniform bounds are desired; no compactness assumption outside those explicitly stated here
on supports in relative variables and the separation/rate assumptions supplied for the readings.
Refining one block in an annular patch, all positions, dimensions, centers, common length persist.
**An aperture for positions relative to the detectors is not a relative separation** between
current groups. Group separations needed by the *reader*, including all subsequent ones on the
shrinking normalized apertures, are proved independently e.g. for an initial patch with strict
groups or when standing up a reader from a parent resolution to a child resolution.
-/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.Contacts.Harvest
open Function Filter Set Metric MeasureTheory Submodule Normal
open scoped Classical Topology BigOperators ContDiff InnerProductSpace
-- `Group` notation shadow; do we need abbrev?
variable {k : ℕ} {W I E : Type} [NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
variable {g : Normal.Group k}
structure Route (P : E→ₗᵢ[ℝ] Points k) (Q : Pieces g) (I W : Type) where
   ceiling : ℝ
   allows : ceiling∈ Ioc 0 1
   length : W→ℝ
   offset : W→ Points k
   diameter : I → W→ ℝ
   frame : W→ E≃L[ℝ] E
   stage : W → Set E
   register : Normal.Group k → I
   tagalong : ℝ
   leading : 1 ≤ tagalong
   reserve : ℝ
   positive : 1 ≤ reserve
   short w : 0< length w ∧ 2 * length w ≤ ceiling
   accounted i w : diameter i w∈ Ioc 0 1
   aligned w i : i∈ Q.parts → Collapsed i (offset w)
   displaysNormals i : i∈ Q.parts → plane i ≤ LinearMap.range P.toLinearMap
   accommodates (w : W) i : i∈ Q.parts → Proper (frame w) (diameter (register i) w) (normalOn P i)
   in_budget (w) i : i∈ Q.parts → 1< i.card → diameter (register i) w ≤ tagalong * length w
   limited_stage w : stage w ⊆ limited (frame w) reserve
   closedStage w : IsClosed (stage w)
   clear (w) i : i∈ Q.parts → stage w ⊆ strip (normalOn P i) ceiling

namespace Route
variable {P:E→ₗᵢ[ℝ] Points k} {Q : Pieces g} (r : Route P Q I W)
variable (i : Q.parts)
local notation "G" => Normal.Group k
local notation "L" => normalOn P i.val

def actualAt (w:W)(x:E) := P x + r.offset w
lemma actualPoint (w:W)(x:E) (j:Fin k) : r.actualAt w x j= (P x) j+r.offset w j:= rfl
def R (v : Normal.Group k) := r.diameter (r.register v)
lemma valid (j:G) (w:W): r.R j w∈ Ioc 0 1:= r.accounted _ _
lemma scaling_frame (w) : Proper (r.frame w) (r.R i.val w) (L):= r.accommodates w _ i.property
lemma proportions (w) : r.stage w ⊆ strip (normalOn P i.val) (r.R i.val w*r.reserve):= (r.limited_stage w).trans (rel_limit _ (r.scaling_frame i w) (r.valid _ _).1)
lemma fitted (w)(t : Bool) : halo L (r.length w) t (r.stage w) ⊆ strip L r.ceiling:= tail_hug _ (r.clear w i.val i.property) (r.short w).2
variable (t : Bool) -- need move past?

/-- Angular patch at one root and estimated halo. `t` means projected branch of i. -/
def site (u : Fans P i.val)(v : Splittings i.val)(w:W) (a : ℝ) := halo L (r.length w) t (r.stage w) ∩ u.patch v a
lemma closeds (u v w a) : IsClosed (r.site i t u v w a):= (halo_closes _ (r.closedStage w) _).inter (u.ray_closes v a)
lemma shadeLifts (u v w a) : r.site i t u v w a ⊆ halo L (r.length w) t (r.stage w):= inter_subset_left
lemma shadesCover (u v w a) : r.site i t u v w a ⊆ halo L (r.length w) t (r.stage w) ∩ sun L a:= inter_subset_inter (by rfl) inter_subset_left
lemma sun_shade (u v w a) : r.site i t u v w a ⊆ u.patch v a:= inter_subset_right
lemma horizon (u v w a) : r.site i t u v w a ⊆ strip L r.ceiling:= (r.shadeLifts ..).trans (r.fitted ..)

def last := 2*(r.tagalong*r.reserve+2)
lemma spends_to : r.tagalong ≤ r.last:= by
   have he:= le_mul_of_one_le_right ((zero_le_one.trans r.leading)) r.positive; unfold last; linarith only [he,r.leading]
lemma active (u : Fans P i.val) (q w a) (h : (r.site i false u q w a).Nonempty): a ≤ (2*r.reserve)*r.R i.val w:= by
   obtain ⟨x,hx⟩:=h; have he : a/2 ≤ ‖(normalOn P i.val).starProjection x‖:= hx.2.1.1; have hh : ‖(normalOn P i.val).starProjection x‖ ≤ r.R i.val w * r.reserve:= r.proportions i w hx.1; linarith only [he,hh]
lemma stay_pay (hp : 1 < i.val.card) (u : Fans P i.val) (q w a) (h : (r.site i t u q w a).Nonempty): a ≤ r.last*r.length w:= by
   obtain ⟨x,hx⟩:= h; have hv:= (r.short w).1; have hr:0≤ r.reserve:= zero_le_one.trans r.positive;
   have hh:r.stage w ⊆ strip L (r.length w*r.tagalong*r.reserve):= fun x hx=> le_trans (r.proportions i w hx) (mul_le_mul_of_nonneg_right (le_trans (r.in_budget _ _ i.property hp) (mul_comm _ _).le) hr)
   have hh'(b : ℝ)(hn:0≤b) (hy : (b=(r.length w*r.tagalong*r.reserve) ∨ b=2*r.length w) ∧ ‖(normalOn P i.val).starProjection x‖ ≤ b) : a ≤ r.last*r.length w:= by
       have hp:= hy.2; have he : a/2 ≤ ‖(normalOn P i.val).starProjection x‖:= hx.2.1.1; unfold last; rcases hy.1 with h|h; subst b; linarith only [hp,he,hv]
       subst b; linarith only [hp,he,mul_nonneg ((mul_pos hv (zero_lt_one.trans_le r.leading)).le) hr] -- nested ring
   have hstep : x∈r.stage w → a ≤ r.last*r.length w:= fun hw=> hh' _ (mul_nonneg (mul_pos hv (zero_lt_one.trans_le r.leading)).le hr) ⟨Or.inl rfl,hh hw⟩
   cases t; exact hstep hx.1; exact Or.elim hx.1 hstep (fun hl=> hh' _ (mul_pos two_pos hv).le ⟨Or.inr rfl, hl.2⟩)

-- the 'window' for IH repeated, even when empty across some geometries.
abbrev ramp (u v) := {p : W×ℝ // p.2 ∈ Ioc (0:ℝ) 1 ∧ (r.site i t u v p.1 p.2).Nonempty}
-- not abbrev? operations use .val.

variable (u : Fans P i.val)(v : Splittings i.val)
local notation "W'" => r.ramp i t u v
variable (h : 1 < i.val.card)
def renew : Route P (replace i v.val) (Option I) (r.ramp i t u v) where
   ceiling:= r.ceiling
   allows:= r.allows
   length b:=r.length b.val.1
   offset b:=r.offset b.val.1
   diameter j b:= j.elim b.val.2 (fun j=> r.diameter j b.val.1)
   register j:= if j∈ v.val.parts then none else some (r.register j)
   frame b:= relaunch L (r.frame b.val.1) b.val.2 (r.R i.val b.val.1) b.property.1.1 (r.accounted _ _).1
   stage b := r.site i t u v b.val.1 b.val.2
   tagalong := r.last
   leading := r.leading.trans r.spends_to
   reserve := 2+r.reserve
   positive:= le_trans r.positive (le_add_of_nonneg_left zero_le_two)
   short b:= r.short b.val.1
   accounted j b:= j.casesOn b.property.1 (fun a=> r.accounted a _)
   aligned b j:= by
      intro hj; rw [replace_parts] at hj; exact (Finset.mem_union.mp hj).elim (fun hf=> r.aligned _ _ (Finset.mem_erase.mp hf).2) (fun hg=> (r.aligned _ _ i.property).subgroups (v.val.le hg))
   displaysNormals j:= by intro hj; rw [replace_parts] at hj; exact (Finset.mem_union.mp hj).elim (fun ht=> r.displaysNormals j (Finset.mem_erase.mp ht).2) (fun h=> (plane_le (v.val.le h)).trans (r.displaysNormals i.val i.property))
   accommodates b j:= by
      intro hj; rw [replace_parts] at hj; by_cases he : j∈ v.val.parts
      · rw [if_pos he]; exact (launched _ (r.scaling_frame i _) _ _).within (normal_le P (v.val.le he))
      obtain ⟨hh,hy⟩:= Finset.mem_erase.mp ((Finset.mem_union.mp hj).resolve_right he); rw [if_neg he]; exact (r.accommodates _ j hy).aside _ _ (normals_distinct P (Q.disjoint hy i.property hh))
   in_budget b j:= by
      intro hj hw; rw [replace_parts] at hj; by_cases he:j∈ v.val.parts; rw [if_pos he]; exact r.stay_pay i t h u v _ _ b.property.2
      rw [if_neg he]; exact (r.in_budget _ j (Finset.mem_erase.mp ((Finset.mem_union.mp hj).resolve_right he)).2 hw).trans (mul_le_mul_of_nonneg_right r.spends_to (r.short _).1.le)
   limited_stage b := (r.shadesCover ..).trans (farther _ (r.limited_stage _) (r.scaling_frame i _) _ _)
   closedStage b:= r.closeds ..
   clear b j:= by
      intro hj; rw [replace_parts] at hj; by_cases he:j∈ v.val.parts; exact (r.horizon ..).trans (inherit_strip _ (normal_le P (v.val.le he)))
      obtain ⟨hh,hy⟩:= Finset.mem_erase.mp ((Finset.mem_union.mp hj).resolve_right he); exact (r.shadeLifts ..).trans (inherit_halo _ (normals_distinct P (Q.disjoint hy i.property hh |>.symm)) t (r.clear _ _ hy))

-- dot arguments order? renew h required implicit? include?
lemma R_here {j:G} (he:j∈ v.val.parts)(w : W') : (r.renew i t u v h).R j w=w.val.2:= by unfold R renew; dsimp; rw [if_pos he]; rfl
lemma R_there {j:G} (he:j∉ v.val.parts)(w:W') : (r.renew i t u v h).R j w=r.R j w.val.1:= by unfold R renew; dsimp; rw [if_neg he]; rfl
end Route
end YM.Contacts.Harvest
