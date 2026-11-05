import Mathlib.Data.Set.Finite.List
import YM.Push.FREE_RESOLVENT.ListJets
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Completion


/-! # Comparing the covariance tables on a subpatch

For localization/reconnection applications while still on the single-step
integral. Include a genuine unified predicate here on geometry, V links
and tags/k choices sufficient for agreement through *actual table reads*, not
assuming a comparison result on the matrices. Does not assert that
these are all the reads needed for determining a branch/occurrence
eligibility in the final density. Include final halo for flag predicates
there too. Here use initial sites/distinct pointers, with estimates leaving
slack to include edge endpoints (per downstream geometry).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.NonflatCovarianceLocality.Matching
open Function Filter Lattice RG Pressure Precision Wilson Tree Matrix
open Next.SectorChange Next.SectorChange.Schur Next.SectorChange.Wisps Next.Fluctuations
open Next.SectorChange.Completion 
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff

variable {G : Gauge} {c f : Side} {S : StepData c f} {x C Y s : ℝ}

/-- Stencil of INPUTS for the one-step D calculation.
V/histories elsewhere can even be changed incompatibly (formulas over all
V always total). No receipt to switch indicators or change masking between
derivatives. `Costs/aisles` are actual recorded store values. Requires
agreement of positive-link values in those stencils according to centers. Allocate even
the endpoints of those V links when actually packaging. -/
structure ReadsWithin (o : Site c) (R : ℕ) (A B : Stores S) (F H : Forest S.ratio)
    (V W : Config G c) (k k' : S.Choices) : Prop where
  sites : AgreeNear id o R V W
  flags i : separation o i ≤ R → (i∈A.flags ↔ i∈B.flags)
  costs p : separation o (S.ratio.parent p.1) ≤ R → (p∈A.costs ↔ p∈B.costs)
  aisles e : separation o e.1 ≤ R → (e∈A.aisles ↔ e∈B.aisles)
  trees x : separation o (S.ratio.parent x) ≤ R → F.up x=H.up x
  choices i : separation o i ≤ R → k.1 i=k'.1 i
  bonds b : separation o b.1 ≤ R → k.2 b=k'.2 b

-- Identity projection on *precisely* the active axes. Support tests still
-- work regardless of which of the two branches will eventually read it.
def engaged (x : ℝ) (A : Stores S) (F : Forest S.ratio) (i : Bond f) : Prop :=
  i∉F.trunks ∧ S.ratio.parent i.1 ∉ A.dome (10*radiusB x) ∧
    S.ratio.parent (i.1+step i.2) ∉ A.dome (10*radiusB x)

lemma fresh_active (x) (A : Stores S) (F : Forest S.ratio) (i : Active A x F) :
    engaged x A F i.val.val :=
  ⟨i.val.property, fun h => i.property (Or.inl h),fun h => i.property (Or.inr h)⟩
lemma fields (x) (A : Stores S) (F : Forest S.ratio) (i : Bond f) :
    engaged x A F i ↔ ∃ j : Active A x F, i=j.val.val := by
  constructor
  · intro h
    let y : Active A x F := ⟨⟨i,h.1⟩,by rw [chill]; exact not_or.mpr h.2⟩
    exact ⟨y,rfl⟩
  rintro ⟨j,rfl⟩; exact fresh_active ..
lemma vacant_pass {x : ℝ} (A : Stores S) (F : Forest S.ratio) (i : vacant A F x G) :
    ¬ engaged x A F i.val.1 := by
  intro h
  obtain ⟨j,hj⟩ := (fields ..).mp h
  exact i.property ⟨(j,i.val.2),Prod.ext hj rfl⟩

variable {A B : Stores S} {F H : Forest S.ratio} {k k' : S.Choices} {V W : Config G c}
  {r l : ℕ} {o o' : Site c}

namespace ReadsWithin
variable (h : ReadsWithin o r A B F H V W k k')
include h

lemma flip : ReadsWithin o r B A H F W V k' k :=
  ⟨fun i hi => (h.sites i hi).symm, fun i hi => (h.flags i hi).symm,
    fun i hi => (h.costs i hi).symm,fun i hi => (h.aisles i hi).symm,
    fun i hi => (h.trees i hi).symm,fun i hi => (h.choices i hi).symm,fun i hi => (h.bonds i hi).symm⟩


private lemma one_place {v : Site c} (H : separation o v+3 ≤ r) (hA : v∈A.place) : v∈B.place := by
  rcases Finset.mem_union.mp hA with hL|hL
  · rcases Finset.mem_union.mp hL with he|he
    · obtain ⟨x,hx,hv⟩ := Finset.mem_biUnion.mp he
      obtain ⟨i,hi,hy⟩ := Finset.mem_image.mp hv
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨x,(h.costs x ?_).mp hx,hv⟩))
      apply le_trans (separation_triangle o v (S.ratio.parent x.1))
      rw [separation_comm v,← hy]
      rw [← hy] at H
      have he := Work.E04.parent_separation S.ratio x.1 i
      have ht := Work.E01.sep_touched x i hi; omega
    obtain ⟨e,he,hv⟩ := Finset.mem_biUnion.mp he
    refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨e,(h.aisles e ?_).mp he,hv⟩))
    have he : separation v e.1 ≤ 1 := by
      simp only [pinPos, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with hv|hv <;> subst v
      · simp
      rw [separation_comm]; exact Work.E03.sep_step ..
    have hh := separation_triangle o v e.1; omega
  exact Finset.mem_union_right _ ((h.flags v (by omega)).1 hL)

private lemma one_dome {v : Site c} (b : ℕ) (H : separation o v+b+3 ≤ r)
    (hA : v∈A.dome b) : v∈B.dome b := by
  obtain ⟨x,hx,hi⟩ := halo_spec.mp hA
  apply halo_spec.mpr ⟨x,h.one_place _ hx,hi⟩
  have he := separation_triangle o v x; rw [separation_comm v] at he; omega
lemma domes {v : Site c} (b : ℕ) (H : separation o v+b+3 ≤ r) : v∈A.dome b ↔ v∈B.dome b :=
  ⟨h.one_dome b H,h.flip.one_dome b H⟩
private lemma one_tree {e : Bond f} (hv : separation o (S.ratio.parent e.1)+1 ≤ r)
    (he : e∈F.trunks) : e∈H.trunks := by
  obtain ⟨i,hi,hy⟩ := (F.trunk_mem_iff _).mp he
  have hb : F.up i=H.up i := by
    apply h.trees
    have ht : separation (S.ratio.parent e.1) (S.ratio.parent i) ≤ 1 := by
      rw [← hy]; unfold Step.used; split
      · have hh := Work.E03.parent_step S (i-step (F.up i).dir) (F.up i).dir
        rw [sub_add_cancel] at hh; exact hh
      simp
    have hg := separation_triangle o (S.ratio.parent e.1) (S.ratio.parent i); omega
  exact (H.trunk_mem_iff _).mpr ⟨i,hi,hb ▸ hy⟩
lemma tree {e : Bond f} (hv : separation o (S.ratio.parent e.1)+1 ≤ r) :
    e∈F.trunks ↔ e∈H.trunks := ⟨h.one_tree hv,h.flip.one_tree hv⟩
lemma enabled (x : ℝ) {e : Bond f} (he : separation o (S.ratio.parent e.1)+10*radiusB x+4 ≤ r) :
    engaged x A F e ↔ engaged x B H e := by
  have hZ := separation_triangle o (S.ratio.parent e.1) (S.ratio.parent (e.1+step e.2))
  have hv := Work.E03.parent_step S e.1 e.2
  unfold engaged
  rw [h.tree (by omega),h.domes _ (by omega),h.domes _ (v:=S.ratio.parent (e.1+step e.2)) (by omega)]
lemma alignment {s : Signed} {p : Where S} (x : ℝ)
    (he : separation o (s.act (roots S p)) + span S.patch x+10*radiusB x+4 ≤ r) :
    curb (shots S x) A F x s p ↔ curb (shots S x) B H x s p := by
  have hS (e : Bond f) (hx : e∈shots S x s p) : engaged x A F e ↔ engaged x B H e := by
    have hl := separation_triangle o (s.act (roots S p)) (S.ratio.parent e.1)
    have hv := (contains ..).1 hx; exact h.enabled x (by omega)
  constructor
  · rintro ⟨i,hi⟩
    obtain ⟨j,hj⟩ := (fields ..).mp ((hS _ hi).mp (fresh_active ..))
    exact ⟨j,hj ▸ hi⟩
  rintro ⟨i,hi⟩
  obtain ⟨j,hj⟩ := (fields ..).mp ((hS _ hi).mpr (fresh_active ..))
  exact ⟨j,hj ▸ hi⟩
lemma correspond (x : ℝ) (p : Rows.Receipt G S)
    (he : separation o (down S p)+span S.patch x+10*radiusB x+4 ≤ r) :
    Rows.keep x (shots S x) A F p.1 ↔ Rows.keep x (shots S x) B H p.1 := by
  rcases p with ⟨⟨s,j|j⟩,t⟩ <;> exact h.alignment x he
end ReadsWithin
end YM.AnalyticBridge.NonflatCovarianceLocality.Matching
