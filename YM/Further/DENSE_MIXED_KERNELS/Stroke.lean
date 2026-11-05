import YM.Further.DENSE_MIXED_KERNELS.Witness

/-!
# Principal, companion, and rough pigment

Pad inputs have to match the component formula even after dropping defaults.
Keep H/K masked evaluations (same `L.entries`) through variants. Choose
footprints for marked UI calls and coordinates on actual Z list; overlaps/
locality of the calls & stencil/geometry reserves still need to be supplied.
Exact eligibility/location rules for replacing an E are open. These results
show e.g. the principal term protected expression under a guard input and how
to recover raw via its companions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Set MeasureTheory Measure Lattice RG Wilson Precision Module Pads
open Port Gaussian Surface Tree Push.SectorMeasure
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

-- windows and deterministic table geometry of one occurrence. Blank variant =
-- push raw χ protections through existing (e.g. H and all step eligibility
-- checks needed separately). Principal/comp pay BOTH even on small footprints.
inductive Cycle (ι : Type*) (κ : Type*)
  | principal (I : Finset (ι⊕κ))
  | companion (I : Finset (ι⊕κ)) (witness : I)
  | blank

structure Stroke (ι : Type*) (κ : Type*) where
  J : Finset ι
  z : Cycle ι κ

namespace Stroke
variable {ι κ Ω : Type} [Fintype ι] [Fintype κ]
    {G : Gauge} {A : ChartRatio G} {H : Port A} {S : Surface H ι κ Ω}
    (s : Stroke ι κ) (χ : Chi)

def I := match s.z with | .principal x|.companion x _ => x | .blank => (∅:Finset (ι⊕κ))

def sem (d : ℝ) (z : H.front ι (H.Room κ)) := match s.z with
  | .blank => (1:ℝ) | .principal x => middle H χ d x z | .companion x i => endCap H χ d x i.val z

def mark (D : Stroke ι κ) (S : Surface H ι κ Ω) (c : Chi) (g w d : ℝ) (y : Ω × H.front ι (H.Room κ)) : ℂ :=
    ↑(pool S c g w D.J y*D.sem (H:=H) c d y.2)

omit [Fintype ι] [Fintype κ] in
lemma valued (d : ℝ) (x : H.front ι (H.Room κ)) : 0 ≤ s.sem (H:=H) χ d x ∧ s.sem (H:=H) χ d x≤1 := by
  unfold sem; split
  · norm_num
  next i => exact warmth ..
  next i y => exact shade_bounds H χ _ _ _ _ i.property





variable {n : Side} {W : Config G n → Surface H ι κ Ω}
    {U : Config G n} {P : Directions G n → Prop} {g w d T : ℝ} {k : ℕ} {p : Ω × H.back ι (H.Room κ)}

-- Per post-l costs independent of origin. Use B cert to size x and J


def temper (D : Stroke ι κ) (H : Port A) (c : Chi) (k : ℕ) (T : ℝ) := D.J.card*stepRate H c k T+D.I.card*speed H c k T
omit [Fintype ι] [Fintype κ] in
lemma helpful (ht : 0≤T) : 0 ≤ temper s H χ k T := add_nonneg (mul_nonneg (Nat.cast_nonneg _) (step_nonneg _ _ ht))
    (mul_nonneg (Nat.cast_nonneg _) (sunnier _ _ ht))



-- purchasing at Pre support rule; can insert identically
lemma held (hw : 0<w) {u : Ω × H.front ι (H.Room κ)} (h : s.mark S χ g w d u ≠ 0) :
    ∀ i∈s.J, ‖displace S g u i‖< 2*w := by
  unfold mark at h; exact in_pool χ u (left_ne_zero_of_mul (Complex.ofReal_ne_zero.mp h)) hw


end Stroke

section Pigment
open Marker Labels Overlay Extra.Multi
variable {n m : Side} {S : StepData m n} {F : Forest S.ratio} {V : Type} [DecidableEq V] {R : Census V}
    {G : Gauge} {B : Rep G n} (L : Bands R B) {A : ChartRatio G} {H : Port A}
    (X : View H F) (χ : Chi) (i : ℕ)
    (J : Finset X.J) (K : Finset (X.J⊕X.K)) (U : Config G m) {w d : ℝ} (g : ℝ)

-- E-Fpr replacement, strict guard inputs from trusted kernel data needed.
-- `Guard` a per-center evaluation statement; include along whole germs
-- in application. retain separate direct fundamental sector identities.
structure Guard (w d : ℝ) : Prop where
  secure : ∀ p : X.Before, (∀ j∈K,‖Pads.take H j p.2‖ < 2*d) → Healthy B.p.threshold (L.support i) (X.config U g p) ∧
    ∀ j∈J, ‖displace (X.base U) g p j‖ ≤ w


end Pigment
end YM.Further.DenseMixedKernels
