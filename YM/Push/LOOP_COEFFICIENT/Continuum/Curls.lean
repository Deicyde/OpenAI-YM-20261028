import YM.Push.LOOP_COEFFICIENT.Paths.Polynomial
import YM.Push.LOOP_COEFFICIENT.Paths.Wave


/-!
# Exterior polynomials in ordinary fine-wave variables
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Continuum
open Paths Matrix Function Set Filter Lattice Laurent Bloch RG Wilson Work.F02 Complex
open scoped Topology ContDiff BigOperators
variable {G : Gauge}

abbrev Polarization (G : Gauge) := CSpace (Axes G)
abbrev Corners (G : Gauge) := Axis → Axis → CColor G

def shaft (i : Axis) : Polarization G →ₗ[ℂ] CColor G := LinearMap.pi fun j => LinearMap.proj (i,j)


def freq (q : Momentum) (i : Axis) := I * q i



def arc (x y : Polarization G) : Corners G := fun i j => cAd G (shaft i x) (shaft j y)





variable {k : ℕ} (p : Fin k → Momentum) (v : Fin k → Polarization G)

def sourceField (i : Axis) : CSpace (Fin k) →ₗ[ℂ] CColor G := ∑ j,(LinearMap.proj j).smulRight (shaft i (v j))

def sourceD (x : Cover) (i : Axis) : CSpace (Fin k) →ₗ[ℂ] CColor G := ∑ j,wind (p j) x • (LinearMap.proj j).smulRight (shaft i (v j))

def curlSquare (i : PlaqAxes) : Square (CSpace (Fin k)) (CColor G) where
  one := (sourceD p v (step i.val.1) i.val.2 - sourceD p v (step i.val.2) i.val.1).toContinuousLinearMap
  two := (LinearMap.toContinuousLinearMap.toLinearMap.comp ((cAd G).compl₁₂ (sourceField v i.val.1) (sourceField v i.val.2))).toContinuousLinearMap
  Q := (LinearMap.toContinuousLinearMap.toLinearMap.comp (cDot G)).toContinuousLinearMap
  symm x y := dotProduct_comm x y















end YM.Push.Loops.Continuum
