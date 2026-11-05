import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Centered
import YM.Primitives.SMALL_FIELD_EXTERIOR.Shed
/-!
# Picking the shift pocket and its cutoff

Use full F.order with actual tags, sum on collar support evaluated at ORIGINAL
choice rules (even when the shifted slice is used elsewhere). Outside that range
density with tags used unmodified before integrating. Ball sizes before g, after period.
Selector cutoff part of proof, not activity term for this scale. It doesn't need
to be lattice Local. Smoothness in matrix-linked near fields preserving widths
considered only after radius choices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter  Set Metric Asymptotics MeasureTheory Next.SectorChange.Gaussian
open RG Wilson Precision Lattice  Pressure Work.F05 Tree Matrix
open scoped Matrix Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
open Primitives.SmallFieldExterior.Forestage
variable {G : Gauge} {m n : Side} {S : StepData m n}
variable {B : Forest S.ratio} (k : S.Choices) {p : Clip} {R : PathData G}
    (w : Bid.Dir G m) {u : Bid.Dir G m → AxisChart G B}





-- Use slice compaction only off a neighborhood.
private def size (a : B.Slice G) : ℝ := ∑ i : B.Free,G.price (a i)





def collar (B : Forest S.ratio) (b : ContDiffBump (0:ℝ)) := b ∘ size (G:=G) (B:=B)


variable {η : ℝ}
structure Cutoff (B : Forest S.ratio) (w : Bid.Dir G m) (u : Bid.Dir G m→AxisChart G B) (C : B.Slice G→ℝ) (η : ℝ) : Prop where
  adopted (v) : C v∈Icc 0 1
  inner : ∃ s : ℝ,0<s ∧ ∀ v∈shed B 0 s, C v=1
  sync (v) : C v ≠0 → ∀ k j : S.Choices,S.prediction (B.drape v) k=S.prediction (B.drape v) j
  shift : ∀ᶠ x in 𝓝 0, ∀ a : B.Slice G, C (a * home B w u x)≠0 → a∈shed B 0 η
  prob : Continuous C
  shape : ∃ b : ContDiffBump (0:ℝ), C=collar B b


end YM.PhysicalNext.FlatResponse
