import YM.Next.EXTRACTION.Tails
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.ABSOLUTE_SUMS.Partition
import YM.Work.A15
import YM.Work.B04
import YM.Work.B06

set_option warningAsError false

/-!
# Local marginals on product references

Probability normalization here is intentional (to have coordinate
restriction measure preserving we MUST account for all unused args).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.LogIdentity.Projection
open Lattice Wilson MeasureTheory Function Finset
open scoped BigOperators Topology Classical ENNReal
variable {ι τ : Type*} {α : ι → Type*} [∀ i, MeasurableSpace (α i)] [Fintype ι]
variable (μ : ∀ i,Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]

/-- Measure-preserving even when dropping some coordinates. -/
lemma inject [Fintype τ] (e : τ → ι) (h : Injective e) :
    MeasurePreserving (fun (x : Π i,α i) j => x (e j)) (Measure.pi μ) (Measure.pi fun j => μ (e j)) := by
  let D : Set ι := Set.range e
  let d : τ ≃ D := Equiv.ofInjective e h
  letI : Fintype D := Subtype.fintype (·∈D)
  let f := MeasurableEquiv.piEquivPiSubtypeProd α (·∈D)
  let g := MeasurableEquiv.piCongrLeft (fun i : D => α i.val) d
  have hf : MeasurePreserving f (Measure.pi μ) ((Measure.pi (fun i : D => μ i.val)).prod
      (Measure.pi (fun i : {i // i∉D} => μ i.val))) := measurePreserving_piEquivPiSubtypeProd μ (·∈D)
  have hg := measurePreserving_piCongrLeft (fun i : D => μ i.val) d
  exact hg.symm.comp (measurePreserving_fst.comp hf)

lemma nested (κ : ι → Type*) [∀ i,Fintype (κ i)] (γ : ∀ i,κ i → Type*)
    [∀ i j, MeasurableSpace (γ i j)] (m : ∀ i j, Measure (γ i j)) [∀ i j, SigmaFinite (m i j)] :
    MeasurePreserving (MeasurableEquiv.piCurry γ)
      (Measure.pi fun j : Sigma κ => m j.1 j.2)
      (Measure.pi fun i => Measure.pi (m i)) := by
  let e := MeasurableEquiv.piCurry γ
  change MeasurePreserving e _ _
  suffices h : MeasurePreserving (e.symm) _ _ from h.symm
  refine ⟨e.symm.measurable,(Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
  let t := fun i : ι => Set.univ.pi fun j : κ i => s ⟨i,j⟩
  have he : e.symm ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext x; simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,true_implies,t]
    constructor
    · intro h i j; exact h ⟨i,j⟩
    rintro h ⟨i,j⟩; exact h i j
  rw [he,Measure.pi_pi,Fintype.prod_sigma]
  apply prod_congr rfl; intro i _
  exact Measure.pi_pi _ _

section Gather
variable {κ : τ → Type*} [Fintype τ] [∀ i,Fintype (κ i)] (place : ∀ i, κ i → ι)

/-- Each used address j in each block i has a single physical place.
The condition can be established just from disjoint tested footprints
and no repetitions *between* these marginal-coordinate lists (group
aliases at the place BEFORE invoking this). -/
lemma gather (h : Injective (fun i : Sigma κ => place i.1 i.2)) :
    MeasurePreserving (fun (x : Π i,α i) i j => x (place i j)) (Measure.pi μ)
      (Measure.pi (fun i => Measure.pi fun j => μ (place i j))) := by
  have hh := inject μ _ h
  exact (nested κ (fun i j => α (place i j)) (fun i j => μ (place i j))).comp hh
end Gather
end YM.Push.LogIdentity.Projection
