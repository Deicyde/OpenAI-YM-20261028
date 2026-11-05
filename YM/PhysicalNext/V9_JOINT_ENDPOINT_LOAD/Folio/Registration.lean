import YM.AnalyticBridge.NONFLAT_COVARIANCE_LOCALITY.Portion
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Position
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix

/-!
# Which site hits to count

Stencil certified on the full arrays including tree origins, locations of
sector/table reads even with zero terms, all potential numerical Y/V arguments
on the projection including far frozen bonds or winding paths, and the actual
output V plaquette checks used to price on a *partially* wrong record. Prices
for predictor or K testing elsewhere are separate; no sewing of occurrence
evaluations performed here. No claim this supports changing masks/path data
of T itself. Held χ, d fixed like the rest. Use $η_x$ inside a true exponent only
when actually standing at its output V tests (not allowing a different V
or cut in each call). Hitting theorem later charges the whole `spread`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Folio
open Filter Function Set Lattice RG Wilson Pressure Precision Tree Matrix
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Wisps Schur Push.SectorMeasure
open AnalyticBridge.NonflatCovarianceLocality AnalyticBridge.NonflatCovarianceLocality.Matching
open AnalyticBridge.NonflatCovarianceLocality.Placement
open AnalyticBridge.NonflatCovarianceLocality.Full (point)
open Further.GaussianScalar
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {I : Type} {c f : Side} {G : Gauge} {S : StepData c f} {T : Tube G S} {P : Teller G} {x : ℝ} {A B : Stores S} {F H : Forest S.ratio} {k k' : S.Choices}
    {o : Site c} {r : ℕ} {X : Support c} {p : Paper f} {V W : Config G c} {Y Y' : Config G f} {Z Z' : Prices G (Bond f)} {q : Chi} {d g : ℝ}

structure Postal (X : Support c) (A B : Stores S) (F H : Forest S.ratio) (V W : Config G c) (k k' : S.Choices) : Prop where
  sites : Agrees (X : Set (Site c)) V W
  flags i : i∈X → (i∈A.flags ↔ i∈B.flags)
  costs p : startPos S p ⊆ X → (p∈A.costs ↔ p∈B.costs)
  aisles i : pinPos i ⊆ X → (i∈A.aisles ↔ i∈B.aisles)
  trees i : S.ratio.parent i ∈ X → F.up i=H.up i
  choices i : i∈X → k.1 i=k'.1 i
  bonds i : pinPos i ⊆ X → k.2 i=k'.2 i

def Known (x : ℝ) (A : Stores S) (V : Config G c) (p : Paper f) := ∀ i ∈ clues p, Printed x A V (home S i) (settleR x)

abbrev Neighbours (S : StepData c f) (X : Support c) := (S.ratio.parent ⁻¹' (X : Set (Site c)))

lemma postal_receipt (h : Postal X A B F H V W k k') (hb : halo (r+4) {o}⊆X) : ReadsWithin o r A B F H V W k k' := by
  have he (i : Site c) (hi : separation o i ≤ r) (j : Site c) (hj : separation i j≤4) : j∈X := hb (halo_spec.mpr
    ⟨o,Finset.mem_singleton_self _,(separation_triangle o i j).trans (Nat.add_le_add hi hj)⟩)
  have hp (i : Site c) (hi : separation o i ≤ r) := he _ hi i (by simp)
  have hj (i : Bond c) (hi : separation o i.1 ≤ r) := he _ hi (i.1+step i.2) ((Work.E03.sep_step ..).trans (by decide))
  have hI (i : Bond c) (hi : separation o i.1≤r) : pinPos i⊆X := Finset.insert_subset (hp _ hi) (Finset.singleton_subset_iff.mpr (hj _ hi))
  refine ⟨fun i hi => h.sites i (hp _ hi) (hj _ hi),fun i hi => h.flags _ (hp i hi),fun i hi => h.costs _ ?_,fun i hi => h.aisles _ (hI i hi),fun i hi => h.trees _ (hp _ hi),fun i hi => h.choices _ (hp _ hi),fun i hi=>h.bonds _ (hI i hi)⟩
  intro j hj; obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
  exact he _ hi _ ((Work.E04.parent_separation S.ratio i.1 y).trans (by have ht := Work.E01.sep_touched i y hy; omega))



variable (b : Bulletin x P T)
namespace Bulletin
include b
lemma halos (hw : spread S (padR x) p⊆X) (i : Bond f) (hi : i∈clues p) (hr : r ≤ settleR x+12) : halo r {home S i} ⊆ X := by
  intro j hj
  apply hw; apply (belongs ..).mpr
  obtain ⟨y,hy,hj⟩ := halo_spec.mp hj; obtain rfl := Finset.mem_singleton.mp hy
  exact ⟨i,hi,by have hh:=b.geometry; unfold padR settleR at *; omega⟩

variable (hw : spread S (padR x) p ⊆ X) (h : Postal X A B F H V W k k')
include hw h
lemma posted {i : Bond f} (hi : i ∈ clues p) {a : G.ColorIndex} : ReadsWithin (point S (i,a)) (settleR x +7) A B F H V W k k' :=
  postal_receipt h (b.halos hw i hi (by omega))


variable (hY : Agrees (Neighbours S X) Y Y')
include hY



omit hY in
lemma entries_synced {i : Index G f} (hi : i.1 ∈ clues p) (j : Index G f) :
    here x T A F V k i j=here x T B H W k' i j ∧
    clouds x T A F V k i j=clouds x T B H W k' i j ∧
    gaps x T A F V k i j=gaps x T B H W k' i j := by
  have h₁ := b.clearance_size
  have h₂ : ReadsWithin (point S i) (settleR x+7) A B F H V W k k' := b.posted hw h hi (a:=i.2)
  exact ⟨((accessible b.priced x).both h₂ i (by rw [separation_self]; unfold shiftR mass at h₁; omega) j).1,
    ((cloud_local b.priced b.geometry).both h₂ i (by rw [separation_self]; unfold shiftR at h₁; omega) j).1,
    ((deviations_local b.priced b.geometry).both h₂ i (by rw [separation_self]; unfold farCost shiftR mass at *; omega) j).1⟩
end Bulletin



namespace Bulletin
variable (hw : spread S (padR x) p ⊆ X) (h : Postal X A B F H V W k k')
include b hw h


end Bulletin
end YM.PhysicalNext.JointLoad.Folio
