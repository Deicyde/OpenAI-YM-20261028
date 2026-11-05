import YM.Work.MY3SmoothSeedSectors




/-!
Computed frozen/active geometry for the actual smooth sector.

Frozen means a non-tree physical fine bond with either projected endpoint
in the inclusive 10B seed halo. Active means non-tree and both endpoints
outside that halo. The seed set is the original Stores.place; old K
supports and auxiliary component partitions are not inputs.

The projection is a real diagonal matrix on all physical bond/color
coordinates. Its EuclideanSpace action uses the counting inner product,
not the Pi sup norm of the existing Directions or AxisChart aliases.

The final two distance lemmas are conditional arithmetic consequences of
explicit extent inequalities. They do not construct affine-row stencils
or prove their extent, a spectral gap, or any Gaussian statement.
Source-only proposal; no compiler acceptance is claimed.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.MY3ActiveGeometry

open Lattice Wilson RG Tree Pressure Pressure.Stores
open MY3SmoothSeedSectors
open scoped BigOperators Classical Matrix

variable {G : Gauge} {c f : Side}

def projectedEnds (S : StepData c f) (e : Bond f) : Support c :=
  {S.ratio.parent e.1, S.ratio.parent (e.1 + step e.2)}

def seedSites (S : StepData c f) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) : Support c :=
  (stores S V x choice).place

def nearSeedSites (S : StepData c f) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) : Support c :=
  halo (10 * radiusB x) (seedSites S V x choice)

def NearLink (S : StepData c f) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) (e : Bond f) : Prop :=
  S.ratio.parent e.1 ∈ nearSeedSites S V x choice ∨
    S.ratio.parent (e.1 + step e.2) ∈ nearSeedSites S V x choice

def Frozen (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) (e : Bond f) : Prop :=
  e ∉ F.trunks ∧ NearLink S V x choice e

def Active (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) (e : Bond f) : Prop :=
  e ∉ F.trunks ∧ ¬ NearLink S V x choice e

def frozenLinks (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) : Finset (Bond f) :=
  Finset.univ.filter (Frozen S F V x choice)

def activeLinks (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (x : ℝ)
    (choice : MY3SmoothSeedSectors.Choices c f) : Finset (Bond f) :=
  Finset.univ.filter (Active S F V x choice)

variable (S : StepData c f) (F : Forest S.ratio) (V : Config G c) (x : ℝ)
  (choice : MY3SmoothSeedSectors.Choices c f)



@[simp] lemma mem_frozenLinks (e : Bond f) :
    e ∈ frozenLinks S F V x choice ↔ Frozen S F V x choice e := by
  simp [frozenLinks]

@[simp] lemma mem_activeLinks (e : Bond f) :
    e ∈ activeLinks S F V x choice ↔ Active S F V x choice e := by
  simp [activeLinks]











/-- A second view of the same split, directly on the original Forest.Free. -/
def frozenFree : Finset F.Free :=
  Finset.univ.filter (fun e => NearLink S V x choice e.val)

def activeFree : Finset F.Free :=
  Finset.univ.filter (fun e => ¬ NearLink S V x choice e.val)

@[simp] theorem mem_frozenFree (e : F.Free) :
    e ∈ frozenFree S F V x choice ↔ e.val ∈ frozenLinks S F V x choice := by
  simp [frozenFree, Frozen, e.property]

@[simp] theorem mem_activeFree (e : F.Free) :
    e ∈ activeFree S F V x choice ↔ e.val ∈ activeLinks S F V x choice := by
  simp [activeFree, Active, e.property]











/-- The coordinate type includes tree and frozen links as well as active
ones, with one physical real orthonormal color coordinate per pair. -/
abbrev FineColor (G : Gauge) (f : Side) := Bond f × G.ColorIndex

abbrev CountingSpace (G : Gauge) (f : Side) := EuclideanSpace ℝ (FineColor G f)

def countingProjection : Matrix (FineColor G f) (FineColor G f) ℝ :=
  Matrix.diagonal (fun i => if Active S F V x choice i.1 then 1 else 0)







theorem countingProjection_mulVec (v : FineColor G f → ℝ) (i : FineColor G f) :
    (countingProjection S F V x choice *ᵥ v) i =
      if Active S F V x choice i.1 then v i else 0 := by
  rw [countingProjection, Matrix.mulVec_diagonal]
  by_cases hi : Active S F V x choice i.1 <;> simp [hi]









def projectCounting (v : CountingSpace G f) : CountingSpace G f :=
  WithLp.toLp 2 (countingProjection S F V x choice *ᵥ (fun i => v i))

@[simp] theorem projectCounting_apply (v : CountingSpace G f) (i : FineColor G f) :
    projectCounting S F V x choice v i =
      if Active S F V x choice i.1 then v i else 0 :=
  countingProjection_mulVec S F V x choice (fun j => v j) i









end YM.Work.MY3ActiveGeometry
