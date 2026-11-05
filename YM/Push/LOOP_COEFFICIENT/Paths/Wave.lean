import YM.Push.LOOP_COEFFICIENT.Paths.Angles


/-!
# Simultaneously scaling angular amplitudes and all fine translation momenta
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Matrix Set Lattice Laurent Bloch RG Wilson Work.F02 NormedSpace Complex
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {r : ℕ}

def wind (p : Momentum) (x : Cover) : ℂ := Complex.I*(∑ j,p j*x j)

lemma wind_step (p : Momentum) (i : Axis) : wind p (step i) = I*p i := by simp [wind,step_apply,mul_ite,apply_ite ((↑):ℤ→ℂ)]


variable (p : Fin r → Momentum) (v : Fin r → CSpace (Angles G)) (c₀ : CSpace (Fin r))





def gust (x : Cover) := ∑ j, wind (p j) x • (c₀ j • v j)







def gatherAngle (i : Axis) : CSpace (Angles G) →L[ℂ] CColor G := angle false i + angle true i

def signAngle (a : Step) : CSpace (Angles G) →L[ℂ] CColor G := if a.neg then -gatherAngle a.dir else gatherAngle a.dir


def shearTerm (a : Step) (y : Cover) := complexLie G (signAngle a (gust p v c₀ y))

@[simp] lemma shear_zero (a : Step) : shearTerm p v c₀ a 0 = 0 := by simp [shearTerm,gust,wind]







variable {R : Type} [NormedRing R] [NormedAlgebra ℂ R]




end YM.Push.Loops.Paths
