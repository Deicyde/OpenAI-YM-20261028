import YM.MergeProof.North.Junction
import YM.OPE.Replicas.Fermi

/-!
# Many slots per cell: port of YM/MergeProof/North/Junction.lean

Most of the proof can be shared verbatim with that for pairs. Costs at every step
use the same register though the group being transported can now be quite different.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory Matrix
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Switch
open scoped Topology BigOperators Classical
variable {slotsZ : Type}[Fintype slotsZ][DecidableEq slotsZ] {V ι : Type}[Fintype V][DecidableEq V][Fintype ι]{G:Gauge}{f c:Side}{R:Rep G f}
local notation "X"=> Names V slotsZ
-- Hat lev
variable (M:ι→Hat (Names V slotsZ) R)(c₀ v:V) (b:Equiv.Perm V)(m: Motion)(x: Site f)
structure Kin (P:R.activities.Moves m.1 x)(E:Equiv.Perm ι):Prop where
   here: b c₀=v
   cares i: Focused c₀ (M i).s↔ Focused v (M (E i)).s
   plot i: Focused c₀ (M i).s→ (M (E i)).s=drum b (M i).s ∧ (M (E i)).M=(M i).M.route P ∧ (M (E i)).charge= scalar m (M i).charge
end YM.MergeProof.Ribbons.ManyCopies
