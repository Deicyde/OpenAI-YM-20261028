import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.District

/-!
# Law of the forest choices

The fixed-forest E6 formula cannot be averaged factor by factor just
because it has a sum/integral invariant under changing the tree. Use a
SPECIFIC law with independent choices in the rooted blocks. Include all
fields of that choice (including heights); here proved by exact exchange on
the space of forests. No fixing differing trees in different legs of the
same component. In the sequel `TreesRead` will be about the first Molecule
integral, which we will prove with the native both-end Active set.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Bower
open Function Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree Push.SectorMeasure
open ConnectedActivityE6
open scoped Topology BigOperators Classical

variable {c f : Side} {S : StepData c f}

abbrev forestFintype (S : StepData c f) : Fintype (Forest S.ratio) := by
  haveI := finite_forests (S:=S)
  exact Fintype.ofFinite _
attribute [local instance] forestFintype



def paste (X : Support c) (F H : Forest S.ratio) : Forest S.ratio where
  up i := if S.ratio.parent i ∈ X then F.up i else H.up i
  height i := if S.ratio.parent i ∈ X then F.height i else H.height i
  bound i := by split <;> first | exact F.bound i | exact H.bound i
  rise i hi := by
    by_cases hx : S.ratio.parent i∈X
    · rw [if_pos hx, if_pos (F.stays i hi |>.symm ▸ hx), if_pos hx]; exact F.rise i hi
    rw [if_neg hx, if_neg (H.stays i hi |>.symm ▸ hx), if_neg hx]; exact H.rise i hi
  stays i hi := by split <;> first | exact F.stays i hi | exact H.stays i hi














def allot (g : Forest S.ratio → ℝ) := (Fintype.card (Forest S.ratio):ℝ)⁻¹ * ∑ i,g i








end YM.PhysicalNext.Bower
