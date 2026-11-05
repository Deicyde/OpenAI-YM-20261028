import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.IssuePlan
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Bass
import YM.Work.MY1.NativeActiveParentSandwich





/-!
# Common support/trigger dictionary, principal E singleton

Native sites in `ground` exactly, before h/drop and before dividing any
thermal amounts. Even on E variants with zero current coefficient. `chair`
uses the **two endpoint** mask in both consumers. Does *not* assert that the
Gaussian matrix or reading then agrees: in particular the two constructions
use different window radii and quantifiers! All that is identified here is
the true footprint & eligibility over every possible $V$ read on this branch,
including at equality. Use Psalm for the signed principal inheritance part
and leave any transfer to E6 Gaussian/density considerations separate.
The marked section to open is honest even with exterior flags; they're not
assumed absent globally. Further query support if using a larger family or a
compulsory layout NOT supplied here. Example trigger footprint includes ALL
regular non-tree links meeting either projected endpoint of the full input
read/flag projection (room even for E6 protection calls), in same θ law, not
per-evaluated branch's favorite smaller choice.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat
open Lattice Set MeasureTheory Tree Function Wilson Pressure RG Next.Fluctuations Next.SectorChange
open Push.AbsoluteSums Push.SectorMeasure JointLoad JointLoad.Heir JointLoad.Psalm
open ConnectedActivityE6 ConnectedActivityE6.Shell AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian
open scoped Topology Classical ContDiff Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {c f : Side} {S : StepData c f}

lemma ends_eq (i : Bond f) : ends S i = Work.MY3ActiveGeometry.projectedEnds S i := by
  unfold ends Work.MY3ActiveGeometry.projectedEnds pinPos; simp

lemma cold (X : Stores S) (F : Forest S.ratio) (i : F.Free) (x : ℝ) : active F X (radiusB x) i.val ↔ ¬chill X x F i := by
  unfold ConnectedActivityE6.Shell.active frozen chill; rw [ends_eq]
  simp [Work.MY3ActiveGeometry.projectedEnds,Finset.disjoint_right, i.property]

open Work.MY1.NativeActiveParentSandwich Work.MY3ActiveGeometry in
lemma boundary {V : Config G c} {x : ℝ} {A : Work.MY3SmoothSeedSectors.Choices c f} (F : Forest S.ratio) (i : F.Free)
    (H : i ∈ stemFree S F V x A (10*radiusB x)) (hp : ¬ active F (Work.MY3SmoothSeedSectors.stores S V x A) (radiusB x) i.val) :
    i∈stemFree S F V x A (10*radiusB x) \ stemFree S F V x A (10*radiusB x+1) := by
  refine stem_difference_subset_boundary S F V x A (Finset.mem_sdiff.mpr ⟨H,fun ht=> hp ((cold _ _ i x).2 ?_)⟩)
  exact ((mem_activeLinks ..).1 ((mem_activeFree ..).1 ht)).2

def yFoot (S : StepData c f) (X : Support f) (x : ℝ) (l : ℕ) := Footprint.enlargement S.ratio l (radiusB x) (inspected X)



-- Equivalent exterior-flag reading for the documented evaluations, not an
-- open-neighborhood equality of masks across two different kernels!


section footprint
variable (X : Support f) (x : ℝ) (l : ℕ) (hb : 0<radiusB x) (hl : 500≤l) (F : Forest S.ratio)
abbrev baseRead (S : StepData c f) := Footprint.enlargement S.ratio 0 (radiusB x) (inspected X)

-- travels off the evaluated shield? then refuse this principal layout
variable (A : Stores S)
abbrev Key (F : Forest S.ratio) := {i : F.Free // ¬ Disjoint (baseRead X x S) (ends S i.val) }

include hl hb
private lemma chair_room (i : Key X x F) (y : Site c) (hy : y∈ends S i.val.val) : halo (reach x+4) {y} ⊆ yFoot S X x l := by
  intro w hw; obtain ⟨z,hx,he⟩ := Finset.not_disjoint_iff.mp i.2
  obtain ⟨b,hp,hx⟩ := halo_spec.mp hx
  obtain ⟨e,hy',hw⟩ := halo_spec.mp hw; have hh := Finset.mem_singleton.mp hy'; subst e
  have hzi : separation z y ≤ 2 := ((separation_triangle _ (atEdge S i.val.val) _).trans (Nat.add_le_add_left (by
      rw [separation_comm]; exact Shell.stride _ hy : separation (atEdge S i.val.val) y≤1) _)).trans (Nat.add_le_add_right (stride _ he) _)
  refine halo_spec.mpr ⟨b,hp,(separation_triangle b z w).trans ((Nat.add_le_add hx ((separation_triangle z _ w).trans (Nat.add_le_add hzi hw))).trans ?_)⟩
  have hh:=Nat.mul_le_mul_right (radiusB x) hl; unfold reach; omega

variable (hA : Disjoint A.place (yFoot S X x l))
include hA
lemma hotSeat (i : Key X x F) : active F A (radiusB x) i.val.val := by
  refine ⟨i.val.2, ?_⟩
  rintro hh
  obtain ⟨b,hb',hi⟩ := Finset.not_disjoint_iff.mp hh; obtain ⟨a,ha,h⟩ := halo_spec.mp hb'
  refine Finset.disjoint_left.mp hA ha (chair_room X x l hb hl F i b hi (halo_spec.mpr ⟨b,Finset.mem_singleton_self _,?_⟩))
  rw [separation_comm]; unfold reach; omega

/-- Genuine common footprint, no constructor by resizing on evaluated
V or mask. Even on winding, with earlier flags recomputed in the actual
sieve. -/
def seatsAt : Museum F x A X (yFoot S X x l) (Key X x F) where
  seat := { toFun i := ⟨i.val,(cold A F _ x).1 (hotSeat X x l hb hl F A hA i)⟩
            inj' _ _ h := Subtype.ext (congr_arg (fun e : Active A x F => e.val) h) }
  away := hA
  asks p hp y hy := by
    obtain ⟨_,hp',hx⟩ := halo_spec.mp hy; obtain rfl := Finset.mem_singleton.mp hp'
    have hP := Nat.mul_le_mul_right (radiusB x) hl; exact halo_spec.mpr ⟨_,Finset.mem_image_of_mem _ hp,hx.trans (by unfold reach; omega)⟩
  covers e he _ := ⟨⟨e.val,Finset.not_disjoint_iff.mpr ⟨_,halo_subset _ _ (Finset.mem_image_of_mem _ he),center_end _⟩⟩,rfl⟩
  stores i := chair_room X x l hb hl F i _ (center_end _)

/-- Every possible `plaza` Z call of the E6 singleton, not only those
having nonzero E. -/
lemma access (T : Tube G S) (Y : Coat T F) (hz : Y.seeds=A) (hu : Y.x=x) (i : Bond f) :
    i∈Y.plaza (baseRead X x S) ↔ i∈Set.range (seatsAt X x l hb hl F A hA).address := by
  constructor
  · intro h; obtain ⟨⟨h,hF⟩,hp⟩ := (Finset.mem_filter.mp h).2
    exact ⟨⟨⟨i,h⟩,hp⟩, rfl⟩
  rintro ⟨i,rfl⟩
  apply Finset.mem_filter.mpr; refine ⟨Finset.mem_univ _, ?_, i.2⟩
  change active F Y.seeds (radiusB Y.x) i.val.val; rw [hz,hu]; exact hotSeat X x l hb hl F A hA i
end footprint
end YM.PhysicalNext.Repeat
