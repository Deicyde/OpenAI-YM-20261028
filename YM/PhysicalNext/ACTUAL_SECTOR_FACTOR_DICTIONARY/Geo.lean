import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Map
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Reading
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Postal





/-!
Physical dictionary, shared read convention. Both endpoints, true torus
separations. We compare even across Store and (for local queries we need of
the slice) Forest masks. In a single Roster call the Forest is held fixed.

Use Physical.Reads for V,k (full shared tag),
trunks and seed tables (including negative answers). This suffices for
queries of the local coefficients conditional on that F; not a certificate
of invariant sampling/pricing of different trees. `Refs`: use a padded
*field argument* to compare letters/complete partial arguments from
different charts. No claim that the physical *law* is on all these slots or
that putting anything independent on the unused ones would pay for it!
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Dictionary
open Function Filter Set Lattice RG Wilson Pressure Pressure.Tube Pressure.Stores Tree Precision Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Push.SectorMeasure Push.SectorMeasure.Oriented
open AnalyticBridge.RelativeLogdet AnalyticBridge.Annulus AnalyticBridge.Annulus.Map
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff

namespace Geo
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} {W X : Support c}

lemma halo_over (a b : ℕ) (X : Support c) : halo a (halo b X) ⊆ halo (a+b) X := by
  intro i hi
  obtain ⟨y,hy,hd⟩ := halo_spec.mp hi
  obtain ⟨z,hz,hq⟩ := halo_spec.mp hy
  exact halo_spec.mpr ⟨z,hz,(separation_triangle z y i).trans (by omega)⟩



lemma covers_shield {o : Site c} (a : ℕ) (h : o∈X) : Shields (halo a X) o a :=
  fun _ ht => halo_spec.mpr ⟨_,h,ht⟩

lemma composes {o i : Site c} {a b : ℕ} (h : Shields W o (a+b)) (he : separation o i ≤ b) :
    Shields W i a := h.shift (by omega)

lemma halo_pin {o : Bond c} {r : ℕ} (h : Shields X o.1 r) (hr : 0<r) : pinPos o ⊆ X := by
  intro i hi
  rcases Finset.mem_insert.mp hi with hi|hi
  · exact hi.symm ▸ h.center
  rw [Finset.mem_singleton.mp hi]; exact h _ ((Work.E03.sep_step ..).trans hr)

lemma widen' {o : Site c} {r : ℕ} (h : Shields W o r) (hx : W ⊆ X) : Shields X o r := fun i hi => hx (h i hi)

lemma halo_support {a b : ℕ} (h : X ⊆ halo a W) : halo b X ⊆ halo (a+b) W :=
  Finset.Subset.trans (Corona.halo_mono le_rfl h) (by simpa only [Nat.add_comm] using halo_over b a W)

lemma inspected_radius (X : Support f) : inspected X ⊆ halo 8 X := by
  intro i hi
  rw [inspected,Finset.mem_union] at hi
  rcases hi with h|h
  · exact halo_subset _ _ h
  obtain ⟨q,hq,hi⟩ := Finset.mem_biUnion.mp h
  split at hi
  · simp at hi
  next hh =>
    obtain ⟨z,h,hz⟩ := Finset.not_disjoint_iff.mp hh
    suffices h' : i∈inspected ({z}:Support f) from
      Corona.halo_mono le_rfl (Finset.singleton_subset_iff.mpr h) (Physical.inspect_shield
        (covers_shield 8 (Finset.mem_singleton_self z)) h')
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨q,hq,?_⟩)
    rw [if_neg]; exact hi; simp [hz]

-- All four-dimensional native addresses of a projected X, with parents
-- tested at the origin.





abbrev Reads := @Physical.Reads

variable {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {k k' : S.Choices}



namespace Reads
variable (p : Physical.Reads X A A' F F' V V' k k')
include p
lemma mono (h : W ⊆ X) : Physical.Reads W A A' F F' V V' k k' :=
  ⟨fun i hi ht => p.configuration i (h hi) (h ht),fun i hi => p.frame _ (h hi),
    fun i hx=>p.bond i (Finset.Subset.trans hx h),fun i hi ht=>p.tree i (h hi) (h ht),
    fun i hi=>p.flags i (Finset.Subset.trans hi h), fun i hi=>p.cost i (Finset.Subset.trans hi h),
    fun i hi=>p.aisle i (Finset.Subset.trans hi h)⟩



lemma way {o : Site c} {r : ℕ} (h : Shields X o (r+1)) : TagNe S o r k k' := by
  refine ⟨fun i hi=>p.frame i (h i (by omega)),fun i hi=>p.bond i (halo_pin (composes (a:=1) (by simpa only [Nat.add_comm] using h) hi) (by omega))⟩

lemma visit {o : Site c} {r : ℕ} (h : Shields X o (r+1)) : AgreeNear id o r V V' := by
  intro i hi
  change separation o i.1 ≤ r at hi
  exact p.configuration i (h _ (by omega)) (h _ ((separation_triangle o i.1 _).trans (Nat.add_le_add hi (Work.E03.sep_step ..))))

end Reads

/-- Padded arguments. Restrict to Active/Frozen only at use. -/
abbrev Refs (G : Gauge) (f : Side) := Config G f × Directions G f

/-- Agreement when accessing padded arguments, with more selective
hypotheses than equality on the whole function. For uses only on the
one sector's active/frozen lists can test instead after `paste`. -/
def Yreads (S : StepData c f) (X : Support c) (Y Y' : Config G f) :=
    ∀ e : Bond f,S.ratio.parent e.1∈X → S.ratio.parent (e.1+Lattice.step e.2) ∈ X → Y e=Y' e
def Zreads (S : StepData c f) (X : Support c) (z z' : Directions G f) :=
    ∀ e : Bond f,S.ratio.parent e.1∈X → S.ratio.parent (e.1+Lattice.step e.2)∈X → z e=z' e
structure Same (S : StepData c f) (X W : Support c) (p p' : Refs G f) : Prop where
  frost : Yreads S X p.1 p'.1
  breeze : Zreads S W p.2 p'.2
namespace Same
variable {Y Z : Support c} {p p' : Refs G f} (h : Same S X W p p')
include h
lemma shrink (he : Y ⊆ X) (ht : Z ⊆ W) : Same S Y Z p p' :=
  ⟨fun i hi hh => h.frost i (he hi) (he hh),fun i hi hh => h.breeze i (ht hi) (ht hh)⟩
lemma frozen {i : Bond f} (ht : Shields X (S.ratio.parent i.1) 1) : p.1 i = p'.1 i :=
  h.frost i ht.center (ht _ (Work.E03.parent_step ..))
lemma windy {i : Bond f} (ht : Shields W (S.ratio.parent i.1) 1) : p.2 i = p'.2 i :=
  h.breeze i ht.center (ht _ (Work.E03.parent_step ..))
end Same

end Geo
end YM.PhysicalNext.Dictionary
