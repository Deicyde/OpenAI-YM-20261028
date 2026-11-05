import YM.Next.WARD_BIN.Wheels
import YM.Planned.PRIMARY_INTEGRAL_295.Fizz



/-!
At a real health query. `cardAt` chosen at that point, then **held**
over those chart derivatives. Authority through fixed k pre-L; true t,
threshold ratio and (pre-L, separate from post-L b coefficients)
orders. No arbitrary anchor shifts. Use inductions on whole tuples not
with cost varying uncontrolled over period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Dials
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Nimbuses Dunes Place
open Precision Exterior Tree Streets Porous Carrier Bloch Next.Free Progress.StationaryScenes  Bazaars Launch Shapes
open WardBin.Lies WardBin.Wheels 
open scoped Topology ContDiff BigOperators NNReal Classical Matrix.Norms.Frobenius
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {T : Finset Cover} {k l d : ℕ} {t ξ s M δ u : ℝ} {F : Labels.Frame G d} {c f : Side}
variable {S : StepData c f}
section Proof
-- n point, not whole period. accounting via `oga`. n path variables. =0 permitted.
abbrev Drum (G:Gauge) (n:ℕ) := (Fin n→G.Color) × G.Color
def chant (G:Gauge) (n:ℕ) (x:Fin n→G.Color) := punct n fun i=> G.lieExp (x i)
def forge (G:Gauge) (n:ℕ) (x : Drum G n) := G.plog (G.mat (chant G n x.1 * G.lieExp x.2))
lemma chant_pc (G:Gauge) (n:ℕ) : ContDiff ℝ ω (fun x:Fin n→G.Color=> G.mat (chant G n x)) ∧ chant G n 0=1 := by
  induction n with
  | zero => exact ⟨contDiff_const,rfl⟩
  | succ n ih =>
    have he (x:Fin (n+1)→G.Color) : chant G _ x=chant G n (Fin.tail x)*G.lieExp (x 0):=rfl
    refine ⟨?_,?_⟩
    · simp_rw [he,G.mat_mul]; apply ContDiff.mul
      · apply ih.1.comp; exact contDiff_pi.mpr fun i => contDiff_apply ℝ _ i.succ
      apply G.exp_jet.comp; apply contDiff_apply
    rw [he,show Fin.tail (0:Fin (n+1)→G.Color)=0 from rfl]; simp [ih.2]




structure Knurls (G:Gauge) (k:ℕ) where
  C : ℝ
  r : ℝ
  cap : 1≤C
  opening : 0<r
  sparks : ∀ x:G.El,G.chord x≤2*r → G.lieExp (G.plog (G.mat x))=x ∧ ‖G.plog (G.mat x)‖ ≤ C*G.chord x
  helps : ∀ x:G.El,G.chord x≤r →
     let y:Drum G k := (0,G.plog (G.mat x)); ContDiffAt ℝ k (forge G k) y ∧ Oval.Envelope y k (forge G k) C


namespace Knurls
-- v path terms relative V directed. Constitutive costs.
variable (K : Knurls G k)






end Knurls

-- q already gauged link in this V normalization, derivative computed in fixed link trivialization.

end Proof
end YM.Planned.PrimaryIntegral295.Dials
