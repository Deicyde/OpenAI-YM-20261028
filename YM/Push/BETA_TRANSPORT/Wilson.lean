import YM.Push.BETA_TRANSPORT.Gibbs

/-!
# Wilson partition and source moment response

Same probability Haar per positive link, same one contribution per face, no
rescaling of the color metric. Separate an external β variation of *fixed*
cylinders from any proposed variation of the represented/calibrated fields.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Lattice Wilson RG Gibbs MeasureTheory Filter Set
open scoped Matrix.Norms.Frobenius BigOperators ENNReal NNReal Topology
variable {G : Gauge} {n : Side}

def wilsonCap (n : Side) := (Fintype.card (Face (Per n)) : ℝ) * 2




@[simp] lemma partition_zero (G : Gauge) (n : Side) : partition G n 0 = 1 := Z_zero ..
@[simp] lemma law_zero (G : Gauge) (n : Side) : law G n 0 = prior G n := by
  have he : (weight 0 : Config G n → ℝ≥0∞) = 1 := by ext1 x; simp [weight,bare]
  rw [law,he,withDensity_one]



variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

 -- note: `w` is the very same tilt

-- Keep completeness in all integral APIs.
variable [CompleteSpace X]
set_option linter.unusedSectionVars false











end YM.Push.BetaTransport
