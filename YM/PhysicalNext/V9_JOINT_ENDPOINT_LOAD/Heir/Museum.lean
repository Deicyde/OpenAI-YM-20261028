import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ColourBooks
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Metering
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Completed
import YM.Push.RELAY_MARK.Step
import YM.Push.STRESS_FLUX.Ward
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix
import YM.SectorTools.PHYSICAL_GAUSSIAN_SWITCH.After




/-! # Footprints for pricing an actual principal E expectation

The *supplied* complete read alphabet: required non-tree links INSIDE the
integration stencil are active (deduced from seed separation), in the local
marginal, and have all colors transformed together. Needs the allocated
support to include seats, halos and all actual queries including classification
etc. -- necessary inclusion for THIS calculation given here, not constructing
a choice or shrinking full supports on an expansion. Ambient A,Y can have
unphysical flags/inventories beyond the reads, not inferring licenses or an
integration law for that A from local availability. Payout will require
sizes/temperature on just the actual epoch. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure RG Tree Next Next.SectorChange
    Precision Next.Fluctuations Exterior Bloch Bid AnalyticBridge.LocalGaussianLaws
    AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching AnalyticBridge.NonflatCovarianceLocality.Placement
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {o : Site f} {p : Site c} {S : StepData c f} {A : Stores S} {F : Forest S.ratio} {I : Type}
    {x : ℝ} {X : Support f} {Y : Support c} {V W : Config G c} {k : S.Choices}

abbrev reach (x : ℝ) := 45*(1+radiusB x)

structure Museum (F : Forest S.ratio) (x : ℝ) (A : Stores S) (X : Support f) (Y : Support c) (I : Type) where
  seat : I ↪ Active A x F
  away : Disjoint A.place Y
  asks : ∀ p : Site f, p∈inspected X → halo (reach x+4) {S.ratio.parent p} ⊆ Y
  covers (e : Active A x F) : e.val.val.1∈inspected X → e.val.val.1+step e.val.val.2∈inspected X → e ∈ Set.range seat
  stores i : halo (reach x+4) {S.ratio.parent (seat i).val.val.1} ⊆ Y

namespace Museum
variable (M : Museum F x A X Y I)
abbrev colorSeat (G : Gauge) (M : Museum F x A X Y I) := M.seat.prodMap (Embedding.refl G.ColorIndex)
abbrev address (i : I) := (M.seat i).val.val

lemma address_inj : Injective M.address := fun _ _ h => M.seat.injective (Subtype.ext (Subtype.ext h))
lemma address_range {i : Active A x F} (hi : i.val.val.1∈inspected X) (hj : i.val.val.1+step i.val.val.2∈inspected X) : i.val.val∈Set.range M.address := by
  obtain ⟨z,hz⟩ := M.covers i hi hj; exact ⟨z,congrArg (fun j : Active A x F => j.val.val) hz⟩

include M
lemma admits {i : F.Free} (hi : i.val.1∈inspected X) (hj : i.val.1+step i.val.2∈inspected X) : ¬chill A x F i := by
  have hh (p : Site f) (hp : p∈inspected X) : S.ratio.parent p ∉ A.dome (10*radiusB x) := by
    intro hh; obtain ⟨t,ht,h⟩ := halo_spec.mp hh
    apply Finset.disjoint_left.mp M.away ht
    rw [separation_comm] at h; exact M.asks _ hp (halo_spec.mpr ⟨_,Finset.mem_singleton_self _,by unfold reach; omega⟩)
  exact not_or.mpr ⟨hh _ hi,hh _ hj⟩

abbrev Station (Y : Support c) (x : ℝ) (o : Site c) := halo (reach x) {o}⊆Y
lemma reads_bare (hp : Station Y x p) (h : AgreeNear id p (reach x) V W) (k : S.Choices) : ReadsWithin p (reach x) A (bareStores S) F F V W k k := by
  have he (j) (hj : separation p j ≤ reach x) := hp (halo_spec.mpr ⟨p,Finset.mem_singleton_self p,hj⟩)
  have h' {j} (h : j∈A.place) := Finset.disjoint_left.mp M.away h
  refine ⟨h,fun i hi => ⟨fun h => (h' (Finset.mem_union_right _ h) (he _ hi)).elim,fun h => (Finset.notMem_empty _ h).elim⟩,fun i hi => ⟨fun h => ?_, fun h => (Finset.notMem_empty _ h).elim⟩,
    fun i hi => ⟨fun h => ?_,fun h => (Finset.notMem_empty _ h).elim⟩,fun _ _ => rfl,fun _ _ => rfl, fun _ _ => rfl⟩
  · exact (h' (j:=S.ratio.parent i.1) (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr
        ⟨i,h,Finset.mem_image_of_mem _ (Work.E01.base_touched i)⟩))) (he _ hi)).elim
  exact (h' (j:=i.1) (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,h,by simp [pinPos]⟩))) (he _ hi)).elim
lemma station_valid (h : Healthy (temp x) Y V) (hp : Station Y x p) : Printed x A V p (reach x) := by
  intro j hj; have he := hp (halo_spec.mpr ⟨p,Finset.mem_singleton_self p,hj⟩)
  exact iff_of_false (fun h => Finset.disjoint_left.mp M.away (Finset.mem_union_right _ h) he) (Finset.disjoint_left.mp h he)
lemma asks_origin (ho : o∈X) : Station Y x (S.ratio.parent o) := (Corona.halo_mono (Nat.le_add_right _ 4) (Finset.Subset.refl _)).trans (M.asks _ (Finset.mem_union_left _ ho))
lemma relays (h : Healthy (temp x) Y V) (i : I) : Printed x A V (S.ratio.parent (M.address i).1) (reach x) := M.station_valid h ((Corona.halo_mono (Nat.le_add_right ..) (Finset.Subset.refl _)).trans (M.stores i))

def forwarded (V : Config G c) (h : Healthy (temp x) Y V) : I ↪ Active (amended x A V) x F := {
  toFun i := ⟨(M.seat i).val, by
    have he := (fresh_active x A F (M.seat i))
    let k : S.Choices := Classical.ofNonempty
    have ht := ((Folio.completion_reads (M.relays h i) F k V).enabled x (e:=M.address i) ?_).mp he
    · exact not_or.mpr ht.2
    rw [separation_self]; unfold reach; omega⟩
  inj' := fun _ _ hi => M.seat.injective (Subtype.ext (congrArg (Subtype.val (p:=fun j : F.Free => ¬chill (amended x A V) x F j)) hi)) }
end Museum
end YM.PhysicalNext.JointLoad.Heir
