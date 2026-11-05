import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Manifesto
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.TagsColumnL
import YM.PhysicalNext.RG_NEXT_ALL_FIELD_EXPANSION_DERIVATIVES.Wood

/-!
# Produce the actual averaged gas on its support

Including normalization by terms with Π,Y etc outside: not independent
products of post hoc mixtures. Keep empty flags distinguished, at the
next unforced mask. Allows disjoint luminous records or completely flagged
forest. Unmarked still; any later marker aperture must use same tags too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Bower
open Function Filter Lattice RG Wilson Pressure Pressure.Stores Pressure.Tube Tree Push Push.SectorMeasure
open Precision Finset MeasureTheory ConnectedActivityE6 ConnectedActivityE6.Shell
open ConnectedActivityE6.Census ConnectedActivityE6.Coat ConnectedActivityE6.Matter
open ConnectedActivityE6.Poll ConnectedActivityE6.Pond AbsoluteSums
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius
attribute [local instance] forestFintype

variable {G : Gauge} {c f : Side} {S : StepData c f} {F F' : Forest S.ratio}
variable {P : Teller G} {T : Tube G S} {X : Coat T F} {X' : Coat T F'}
variable {x W C μ v b : ℝ} {Q : ConnectedActivityE6.Target G P} {L : Side} {o : ConnectedActivityE6.Target.Order G W} {R : Rep G f}
variable (H : Cash W x μ L Q o C T R)



def scene (T : Tube G S) (F : Forest S.ratio) (V : Config G c) (x v : ℝ) (χ : Chi) : Coat T F :=
    ⟨⟨∅,∅,∅⟩,x,χ,v,V,Classical.ofNonempty,1⟩

def lumen (R : Rep G f) (T : Tube G S) (x v W a : ℝ) (l : ℕ) (Q : ChartRatio G) (χ : Chi) (s : Molecule S) (V : Config G c) :=
    allot fun F=> proceedsA R (scene T F V x v χ) W a l Q s



include H



end YM.PhysicalNext.Bower
