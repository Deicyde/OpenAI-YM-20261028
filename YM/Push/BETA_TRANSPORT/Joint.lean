import YM.Push.BETA_TRANSPORT.Noise



/-!
# Response of the actually normalized joint block & Wilson source pushforward

Start with the Wilson law with an optional insertion, and block once with the
*same* β, holding S fixed. Both normalizers are configuration-independent
(the tags at each U already have total likelihood one). Coarse densities,
including source densities, are still relative to probability product Haar.
An additional optional **conditional** expectation given V divides by the
full pushed Wilson vacuum density and also has a covariance identity. This
ratio is NOT the normalized cylinder/inserted density of `Source.TransferData`.
No further scalar divisions appear in those transfers (`StepData.push`, previous
module).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius Topology BigOperators
variable {G : Gauge} {c f : Side} (S : StepData c f)

abbrev BothConfigs (G : Gauge) (c f : Side) := Config G f × Config G c



def totalEnergy (t : S.Choices) (p : BothConfigs G c f) := tagEnergy S t p.1 p.2 + energy p.1








variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]









variable [CompleteSpace X]
set_option linter.unusedSectionVars false






















end YM.Push.BetaTransport
