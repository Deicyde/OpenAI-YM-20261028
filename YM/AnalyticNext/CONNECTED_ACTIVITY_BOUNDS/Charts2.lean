import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07



/-!
# Reorient actual links before any affine operations

No new field on a cover. Shared axes and *left* orientation on Lie
increments (requires a base-link factor on negative edges).
Includes exact `barV` commutation, doesn't require V near identity.
These calculations are in support pricing, not proposing a new choice
of history/kernel data.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Turn
open Lattice RG Wilson Precision Pressure Pressure.Stores Tree Function Matrix
 
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n c f : Side}

lemma exp_adjoint (u : G.El) (a : G.Color) : G.lieExp (G.adjoint u a) = u * G.lieExp a * u⁻¹ := by
  apply G.mat_injective
  simp only [G.mat_lieExp,G.mat_adjoint,G.exp_conjugate,G.mat_mul,G.mat_inv]; simp only [Gauge.conjugate]

lemma exp_inverse (a : G.Color) : G.lieExp (-a) = (G.lieExp a)⁻¹ := by
  apply mul_right_cancel (b := G.lieExp a)
  rw [inv_mul_cancel]; apply G.mat_injective
  simp only [G.mat_mul,G.mat_lieExp,map_neg, G.mat_one]
  have ht : Commute (-G.colorMat a) (G.colorMat a) := (Commute.refl _).neg_left
  exact (NormedSpace.exp_add_of_commute ht).symm.trans (by simp)

def edgeP (s : Signed) (e : Bond n) : Bond n := sendEdge s 0 e

lemma pin_map (s : Signed) (e : Bond n) : pinPos (edgeP s e) = (pinPos e).image s.act := by
  rcases e with ⟨x,i⟩
  let I := (posDir i).rotate s
  change pinPos (I.used _) = _
  have he : s.act (step i : Site n)=I.vec := (Step.vec_rotate (R:=Per n) (posDir i) s).symm
  change pinPos (I.used (s.act x+0)) = ({x,x+step i}:Finset (Site n)).image s.act
  simp only [pinPos, Finset.image_insert, Finset.image_singleton, s.act_add, he, add_zero]
  cases I with
  | mk i h =>
    cases h <;> simp [Step.used,Step.vec,sub_eq_add_neg]
    ext; simp [or_comm]

lemma step_transport (s : Signed) (e : Bond n) (V : Config G n) :
    pull s 0 V e = if ((posDir e.2).rotate s).neg then (V (edgeP s e))⁻¹ else V (edgeP s e) := rfl

def maps (s : Signed) (U : Config G n) : Directions G n →ₗ[ℝ] Directions G n :=
  LinearMap.pi fun e => if ((posDir e.2).rotate s).neg then
    -((G.adjoint (U (edgeP s e))⁻¹).comp (LinearMap.proj (edgeP s e)))
    else (LinearMap.proj (edgeP s e))

lemma maps_apply (s : Signed) (U : Config G n) (x : Directions G n) (e : Bond n) :
    maps s U x e = if ((posDir e.2).rotate s).neg then
      -G.adjoint (U (edgeP s e))⁻¹ (x (edgeP s e)) else x (edgeP s e) := by
  unfold maps; rw [LinearMap.pi_apply]
  split <;> rfl

lemma maps_cost (s : Signed) (U : Config G n) (x : Directions G n) (e : Bond n) :
    ‖maps s U x e‖ = ‖x (edgeP s e)‖ := by rw [maps_apply]; split <;> simp [G.norm_adjoint]

lemma operations_pulled (s : Signed) (U : Config G n) (x : Directions G n) :
    pull s 0 (increment U x) = increment (pull s 0 U) (maps s U x) := by
  funext e; rw [step_transport]; simp only [increment,step_transport,maps_apply]; split
  · rw [exp_inverse, exp_adjoint]; group
  rfl



-- Need the parent clause even when step is reversed. Use a helper
-- which doesn't mention the actual rotation.






-- Plot is intentionally *local*, not Alive/Seeded at every chart use.







end YM.AnalyticNext.ConnectedActivity.Turn
