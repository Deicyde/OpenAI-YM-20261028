import YM.Further.DENSE_MIXED_KERNELS.Turning
import YM.Further.DENSE_MIXED_KERNELS.Word


/-!
# Securing slack with patch transactions common to all events
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module
open Source Labels Marker Overlay Extra.Multi
open Port Gaussian Surface Tree
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {Ω ι κ : Type} [MeasurableSpace Ω] [Fintype ι] [Fintype κ] {α β V : Type}
    {G : Gauge} {n m : Side} {A : ChartRatio G} {H : Port A} {W : Config G n → Surface H ι κ Ω}
    {P : Directions G m → Prop} {c C g t r : ℝ} {k q : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]





omit [MeasurableSpace Ω] in
lemma swing_track (S : Surface H ι κ Ω) (p : Ω × H.back ι (H.Room κ)) (hg : 0<g) :
    H.swing g (S.mean p.1) (S.mapUp g p).2.1=S.arc p := by
  change g • (g⁻¹ • (_ - S.mean p.1)) + S.mean p.1 = _
  rw [smul_inv_smul₀ hg.ne', sub_add_cancel]

namespace Word
variable [DecidableEq V] {R : Census V} {S : StepData m n} {F : Forest S.ratio} {x : Chain (α ⊕ β)}
    {A' : Rep G n} {L : Bands R A'} {ρ : α → Pieces} {D : Word H F x L ρ} {U : Config G m}

/-- Together cover all held regular coordinates, even ones queried by a
compulsory packet. We require this of the FACTORS, not even using the
support of H/K. Checked pre kernel switch (any winding). -/
def Caged (D : Word H F x L ρ) (g r : ℝ) (v : Config G m) := ∀ p : D.model.Before,
    (∏ i,D.initial i v p)≠0 → ∀ i, ‖(H.swing g ((D.model.base v).mean p.1) p.2.1) i‖ ≤ r





/-- Give BEFORE integration costs even when on log-extensions that
make Healthy fail. The exponent of `envelope` can be different from W
at evaluation. -/
structure Stretch (D : Word H F x L ρ) (g r : ℝ) (k : ℕ) (U : Config G m) : Prop where
  room : r < H.radius
  slack : ∀ᶠ v in 𝓝 0, Caged D g r (increment U v)
  envelope : let W := D.model.base
    ∃ b c C d t : ℝ, ∃ q : ℕ, 0≤b ∧ 0<c ∧ 1≤C ∧ 0<d ∧ 0≤t ∧ ∀ᶠ v in 𝓝 0,
      let V := increment U v; Glides W V g t k UnitDirs c C ∧
      (∀ i, Measurable (D.post g i V)) ∧
      ∀ y∈(W V).Perch, let z := ((W V).mapUp g y).2
        ∃ u : x.Index → ℝ, (∀ i,Pitch (fun x => D.post g i x y) V UnitDirs k (b * (1+‖z‖)^q*Real.exp (u i)) 1) ∧
          ∑ i,u i ≤ (W V).B y.1 z z - d*‖z‖^2





-- no assumption all validated at one global θ; the controls at evaluation
-- must be paid on these local factor terms with this common law. f TRUE
-- constituents. No derivative taken of K at any input. Require production
-- please see Word.value description.

end Word
end YM.Further.DenseMixedKernels
