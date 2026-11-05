import YM.Progress.CLASSICAL_KIN_RECURSION.Dock


set_option warningAsError false

/-!
# Naturality of the chart functional on auxiliaries. No normalization
cancellation beyond real worth. Freeze constant tag before transfer; may
switch to any others **by Germ proof**.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin.Tent
open Lattice RG Exterior Wilson Precision Tree Bid Bloch Tensor 
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n m : Side} {p : Clip} {W : PathData G}

def label (S : StepData n m):S.Choices:=(fun _=> (S.patch.center,1),fun _=>S.patch.center)

section simple
variable (h : divides n m) (o : Site n)


end simple

section step
variable (h : divides n m) (o : Site n) (P : Patch) (K : KernelChoices)
local notation "S[" n"]"=> dock P K n
local notation "T[" n"]"=> label S[n]








end step
end YM.Progress.ClassicalKin.Tent
