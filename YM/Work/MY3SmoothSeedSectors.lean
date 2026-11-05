import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import YM.Pressure.Seeds



/-!
These overlapping smooth profile sectors are different from the existing
hard thresholdStores partition. Both give pointwise finite identities, but
no equivalence of the two sector records is asserted. Output flags remain
the actual flags. No output flag or threshold indicator is differentiated.

Smoothness of the scalar profile is proved below. Pulling that profile back
through physical fields still requires the stated squared-chord smoothness
gate. In particular, this file does not assert global smoothness of a tagged
predictor across its analytic/fallback branch boundaries.

Source-only proposal for MY1's Lean 4.32/Mathlib81a5 build queue.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Work.MY3SmoothSeedSectors

open Lattice Wilson RG Pressure Pressure.Stores

open scoped BigOperators Classical

variable {G : Gauge} {c f : Side}

/-- Smooth, nonincreasing, one through 1 and zero from 4. -/
def chi (s : ℝ) : ℝ := Real.smoothTransition ((4 - s) / 3)













def defaultProfile (τ r : ℝ) : ℝ := chi ((r / τ) ^ 2)

def chosenProfile (τ r : ℝ) (selected : Bool) : ℝ :=
  if selected = true then 1 - defaultProfile τ r else defaultProfile τ r

















/-- One independent default/nondefault choice at every physical fine
plaquette and coarse noise bond. Flags are not additional profile choices. -/
abbrev Choices (c f : Side) := (Cell f → Bool) × (Bond c → Bool)

def profile (S : StepData c f) (U : Config G f) (k : S.Choices)
    (V : Config G c) (x w : ℝ) (a : Choices c f) : ℝ :=
  (∏ p : Cell f, chosenProfile (fiery G x S.patch.L / 4) (toll U p) (a.1 p)) *
    ∏ b : Bond c, chosenProfile (w * fiery G x S.patch.L)
      (wire (S.prediction U k) V b) (a.2 b)

def stores (S : StepData c f) (V : Config G c) (x : ℝ) (a : Choices c f) :
    Stores S :=
  ⟨Finset.univ.filter (fun p => a.1 p = true),
    Finset.univ.filter (fun b => a.2 b = true), RG.flags (temp x) V⟩













end YM.Work.MY3SmoothSeedSectors
