import YM.Push.LOOP_COEFFICIENT.AliasJets
import YM.Push.LOOP_COEFFICIENT.ChargeStrip
import YM.Push.LOOP_COEFFICIENT.Continuum.Matrix
import YM.Push.LOOP_COEFFICIENT.Continuum.Products
import YM.Push.LOOP_COEFFICIENT.ContinuumTrace
import YM.Push.LOOP_COEFFICIENT.Fine.Root
import YM.Push.LOOP_COEFFICIENT.Paths.Vertex


/-!
# Momentum-polynomial matrices in the annular color convention
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Continuum
open Function Filter Set Matrix Complex Lattice Bloch Wilson RG Work.F02 Paths Fine
open scoped Topology BigOperators ContDiff Kronecker Matrix.Norms.L2Operator
variable {G : Gauge}






def vectorFree (G : Gauge) (W : PathData G) (q : Clip) := (localVertex W q).add ((root G).mul (root G).transpose)
def ghostFree (G : Gauge) := (root G).transpose.mul (root G)

structure Drawing (b : Type) [Fintype b] [DecidableEq b] where
  one : Momentum → ℂ → Matrix b b ℂ
  two : Matrix b b ℂ
  cont : Continuous (uncurry one)
  scale z q t : one (z • q) (z*t) = z • one q t

def Drawing.flat {b : Type} [Fintype b] [DecidableEq b] (D : Drawing b) (k : E4) (t : ℂ) : Reading b :=
    ⟨(disc k 0)⁻¹ • 1,(disc k t)⁻¹ • 1, D.one (radians k) t,D.one (radians k+t • unitAxis 0) (-t),D.two⟩

def scalarLine (a : G.Color) : Drawing G.ColorIndex where
  one k _ := (-2 * I * k 1) • carrier a
  two := (-2:ℂ) • (carrier a)^2
  cont := by unfold Function.uncurry; fun_prop
  scale z q t := by rw [smul_smul]; simp only [Pi.smul_apply,smul_eq_mul]; congr 1; ring

def vectorLine (a : G.Color) : Drawing (Axes G) where
  one k t := (-2 * I * k 1) • ((1:Matrix Axis Axis ℂ) ⊗ₖ carrier a) + (2*I*t) • (spinPlane ⊗ₖ carrier a)
  two := (-2:ℂ) • ((1:Matrix Axis Axis ℂ) ⊗ₖ (carrier a ^2))
  cont := by unfold Function.uncurry; fun_prop
  scale z q t := by rw [smul_add,smul_smul,smul_smul]; simp only [Pi.smul_apply,smul_eq_mul]; congr 2 <;> ring






variable {W : PathData G} {c : Clip} {σ C Λ : ℝ} {b : Type} [Fintype b] [DecidableEq b]
structure LeadingInk (T : G.Color) (V : Vertex (Axes G) b b) (D : Drawing b) : Prop where
  base q : Lead 2 (fun t => V.base (t • q)) (momentumSq q • 1)
  one q s : Lead 1 (fun t : ℂ => V.one (t • q) ((t*s) • unitAxis 0) (needle (colorUp G T))) (D.one q s)
  two q p : Lead 0 (fun t : ℂ => V.two (t • q) (-(t • p)) (t • p) (needle (colorUp G T)) (needle (colorUp G T))) D.two



end YM.Push.Loops.Continuum
