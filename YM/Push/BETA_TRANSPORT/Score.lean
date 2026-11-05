import YM.Push.BETA_TRANSPORT.Gibbs

/-! Summing scored contributions before any further mass division. Covariances are real
score vs vector insertion (ordinary multiplication by score; no source conjugation). -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.BetaTransport
open Gibbs MeasureTheory Filter
open scoped Topology
variable {α τ X : Type*} [MeasurableSpace α] [Fintype τ] [NormedAddCommGroup X] [NormedSpace ℝ X]



def insertEnergy (H : τ → α → ℝ) (F : τ → α → X) : τ → α → X := fun i x => H i x • F i x



structure Scores (w : ℝ → τ → α → ℝ) (H : τ → α → ℝ) (e : ℝ → ℝ) (A : ℝ) (C : ℝ → ℝ) : Prop where
  weight (i) : WeightEstimate (w · i) (fun b x => w b i x * (e b - H i x)) A C
  energy (i) : EnergyEstimate (H i) A

namespace Scores
variable {w : ℝ → τ → α → ℝ} {H : τ → α → ℝ} {e C : ℝ → ℝ} {A : ℝ} {μ : Measure α}
  (h : Scores w H e A C)
include h

omit [Fintype τ] in
lemma comp {γ : Type*} [MeasurableSpace γ] {f : γ → α} (hf : Measurable f) : Scores
    (fun b t x => w b t (f x)) (fun t x => H t (f x)) e A C :=
  ⟨fun i => (h.weight i).comp hf,fun i => ⟨(h.energy i).measurable.comp hf,
    fun _ => (h.energy i).nonneg _,fun _ => (h.energy i).bound _,(h.energy i).cap⟩⟩
omit [Fintype τ] in
lemma integrable (b : ℝ) {F : α → X} (hf : Integrable F μ) (t : τ) : Integrable (fun x => w b t x • F x) μ :=
  (h.weight t).smul_integrable b hf
omit [Fintype τ] in
lemma insert_integrable {F : τ → α → X} (hf : ∀ t, Integrable (F t) μ) (t : τ) :
    Integrable (insertEnergy H F t) μ := (hf t).bdd_smul A (h.energy t).measurable.aestronglyMeasurable
      (Eventually.of_forall (h.energy t).norm_le)



variable [CompleteSpace X]






variable [IsFiniteMeasure μ]




end Scores
end YM.Push.BetaTransport
