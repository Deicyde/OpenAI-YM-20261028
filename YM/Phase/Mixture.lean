import YM.OS.Slabs
import YM.Euclid.Stress
import Mathlib.Topology.Algebra.StarSubalgebra

/-!
# Phase representation criteria, not arbitrary vacuum postulates

Characters of the actual compression algebra devoted to H₀ of *the same table*,
unselected still available. We ask for representation by compact metric spectrum
and faithfulness/full support as claimed by E. M calculations for ANY shifted slab (“phase”
also refers to its place as a representative component); actual barycenter follows.
Counts from slabs stored separately on S and selected phase H0. No coincident probes enter
this construction, no inference from positivity alone.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OS
open Function Set Filter MeasureTheory
open Analysis Word
open scoped Topology NNReal BigOperators InnerProductSpace ContDiff ComplexOrder
variable {G : Gauge} {L : Register G} {S : Table L}

namespace Chamber
variable {a : Axis} (C : Chamber S a)

abbrev H : Hilbert := C.GNS.H
abbrev D : Submodule ℂ C.H := C.flow.ground
abbrev VacuumOp := C.D →L[ℂ] C.D

def omega : C.H := C.GNS.plant (air a)

def omega0 : C.D := ⟨C.omega, (C.flow.fixed _).2 fun t => (C.atBirth t _).symm.trans
  (congr_arg C.GNS.plant (inAir t))⟩

def UniqueHeat : Prop := ∀ v : C.D, ∃ z : ℂ, z • C.omega0=v

lemma seenOmega (P : Spread C) {d} {w : L.Word} (h : Slab a d w) :
    inner ℂ C.omega (P.place d w C.omega)=S.expect w := by
  unfold omega; rw [P.reads h, C.GNS.measure]
  simp [Table.gram,air, entering,linked,raised,reflect,act,conjugate,carry]
end Chamber

namespace Spread
variable {V : Chamber S timeAxis} (P : Spread V)

def atom (w : L.Word) (d : ℝ≥0) : V.VacuumOp := V.D.orthogonalProjectionOnto.comp ((P.place d w).comp V.D.subtypeL)

def generators : Set V.VacuumOp := {A | ∃ (w : L.Word) (d : ℝ≥0), Slab timeAxis d w ∧ A=P.atom w d}

private theorem boring (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : IsSemitopologicalSemiring (X →L[ℂ] X) := inferInstance
private theorem norms (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X] : ContinuousStar (X →L[ℂ] X) := inferInstance
instance : IsSemitopologicalSemiring V.VacuumOp := boring ↥V.D
instance : ContinuousStar V.VacuumOp := norms ↥V.D
def algebra : StarSubalgebra ℂ V.VacuumOp := (StarAlgebra.adjoin ℂ P.generators).topologicalClosure

def slot (w : L.Word) (d : ℝ≥0) (h : Slab timeAxis d w) : ↑P.algebra :=
  ⟨P.atom w d, StarSubalgebra.le_topologicalClosure _ (StarAlgebra.subset_adjoin ℂ P.generators ⟨_,_,h,rfl⟩)⟩

lemma insertValue (w : L.Word) d (h : Slab timeAxis d w) :
    inner ℂ V.omega0 ((P.slot w d h).val V.omega0) = S.expect w := by
  change inner ℂ V.omega0 (V.D.orthogonalProjectionOnto _) = _
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  exact V.seenOmega P h

structure Resolution where
  X : Type
  [metric : MetricSpace X]
  [sets : MeasurableSpace X]
  [borel : BorelSpace X]
  [compact : CompactSpace X]
  μ : Measure X
  character (x : X) : P.algebra →⋆ₐ[ℂ] ℂ

namespace Resolution
attribute [instance] metric sets borel compact
variable {P} (R : P.Resolution)

structure Out : Prop where
  abelian (x y : P.algebra) : x*y=y*x
  -- full faithful representing measure
  normalized : IsProbabilityMeasure R.μ
  support : R.μ.IsOpenPosMeasure
  onto : Function.Bijective R.character
  values (x) : Continuous (R.character x)
  weak (p : P.algebra) : Continuous (fun x => R.character x p)
  ground (p : P.algebra) : (∫ x, R.character x p ∂R.μ) = inner ℂ V.omega0 (p.val V.omega0)

/-- T defines exactly these whole-word values, not character on individual points. -/
def receives (R : P.Resolution) (T : Table L) (i : R.X) :=
    ∀ (w : L.Word), distinct w → ∀ (s : E4) (d : ℝ≥0) (h : Slab timeAxis d (carry w s)),
      T.expect w = R.character i (P.slot _ _ h)

lemma place_exists {w : L.Word} (h : distinct w) : ∃ (s : E4) (d : ℝ≥0), Slab timeAxis d (carry w s) := by
  classical
  have he : ∀ᶠ t : ℝ in atTop, ∀ i ∈ w, 0 < i.1 timeAxis + t := by
    have ht i (hi : i∈w) : ∀ᶠ t : ℝ in atTop, 0 < i.1 timeAxis+t :=
      (eventually_gt_atTop (-i.1 timeAxis)).mono fun j hj => by linarith
    simpa using (eventually_all_finset w.toFinset).mpr (fun i hi => ht i (by simpa using hi))
  obtain ⟨t,ht⟩ := he.exists
  let u := t • basis timeAxis
  let W := carry w u
  have hy : Positive W timeAxis := by
    refine ⟨still h _,fun i hi => ?_⟩
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hi
    change 0<(p.1 + u) timeAxis; simpa [u] using ht p hp
  have hh : ∀ᶠ t : ℝ≥0 in atTop, ∀ i ∈ W, i.1 timeAxis < (t:ℝ) := by
    have hu i (hi : i∈W) : ∀ᶠ t : ℝ≥0 in atTop, i.1 timeAxis < (t:ℝ) :=
      (NNReal.tendsto_coe_atTop.mpr (tendsto_id (x := (atTop : Filter ℝ≥0)))).eventually (eventually_gt_atTop _)
    simpa using (eventually_all_finset W.toFinset).mpr (fun i hi => hu i (by simpa using hi))
  obtain ⟨d,hv,hh⟩ := (hh.and (eventually_gt_atTop _)).exists
  exact ⟨u,d,hh,hy,hv⟩

theorem barycenter (T : R.X → Table L) (hv : R.Out) (ht : ∀ i, R.receives (T i) i) (he : S.Homogeneous)
    (q : L.Word) (h : distinct q) : (∫ i, (T i).expect q ∂R.μ) = S.expect q := by
  obtain ⟨t,d,Hd⟩ := place_exists h
  simp_rw [show ∀ i, (T i).expect q = _ from fun i => ht i q h t d Hd]
  rw [hv.ground,P.insertValue]; exact invariance he h t
end Resolution
end Spread

/-- `Respects/Reuses`: phase inherits B's quotient and all of its
identities.

Width families unselected + chosen.

No implicit alpha choices later. -/
structure Selection (B : Table L) where
  room : Chamber B timeAxis
  unselected : Spread room
  space : unselected.Resolution
  ensemble : space.X → Table L
  atPoint : space.X
  leaps : Chamber (ensemble atPoint) timeAxis
  slabs : Spread leaps

structure Selection.Certificate {P : DiffPlan S} (R : S.Rotation) (J : S.Stress) (C : Selection S) : Prop where
  lengths : Spread.Laws C.unselected P
  still : ∀ x : C.room.D, ∀ i, C.room.flow.U i x = x
  decomposition : C.space.Out
  chosen (i) : C.space.receives (C.ensemble i) i
  states (i) : (C.ensemble i).Hierarchy
  sym i : R.Oriented (C.ensemble i)
  retains i d : (C.ensemble i).null d=S.null d
  coordinates i : P.Inclusions (C.ensemble i)
  calculus i : P.Derivatives (C.ensemble i)
  flux i : Table.StressLaws (C.ensemble i) J P.deriv R.lie
  goes : Spread.Laws C.slabs P
  heat : C.leaps.UniqueHeat
end YM.OS
