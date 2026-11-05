import YM.Extra.MULTISOURCE_TRAJECTORIES.Stubs

/-!
# Both species of random choices: finite conditional marginals and reads

One site tag per vertex EVEN when computing several incident rows of the
kernel. The actual likelihood has shell/axial costs and a shared-frame system;
the normalization of the bond choices is conditional on the same site tags
(not a product of unconditional bond marginals). Footprints below price every
site and complete route even before knowing the actual branch.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Trajectories.Reverse
open Lattice Wilson RG Function Filter MeasureTheory Finset Patch
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical

section Probability
variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {M : Type*} [AddCommGroup M] [Module ℝ M]






end Probability

variable {G : Gauge} {c f : Side} (S : StepData c f)

def test (P : Patch) := P.sites ∪ univ.biUnion fun i : P.Points =>
    (univ.biUnion fun j : P.Points => univ.biUnion fun l : Lattice.Order => (visits i.val (route i.val j.val l)).toFinset) ∪
      (univ.biUnion fun a : Axis => (visits i.val (List.replicate P.L.val (posDir a))).toFinset)

def pullback (D : Support c) : Support f := D.biUnion fun x => (test S.patch).image (fun y => wrap f y + S.ratio.embed x)



variable {P : Patch} {K : KernelChoices}








end YM.Extra.Trajectories.Reverse
