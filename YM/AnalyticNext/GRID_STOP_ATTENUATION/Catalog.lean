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
import Mathlib.RingTheory.RootsOfUnity.Complex
import YM.Ac.Table
import YM.Bid.Drops
import YM.Next.MULTISOURCE.Collateral
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07

set_option warningAsError false

/-! Re-express a joined signed birth on Multi's aggregate alphabet. Preserve
values on every coarse configuration. In particular keep the real gas
inventory and its overlap convention unaltered. The `Legible` assertion
in this compression does *not* buy blanks for the later `imprint`!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Compile
open Function Finset RG Lattice Wilson Marker Overlay Multi MeasureTheory
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {V : Type} [Fintype V] [DecidableEq V] {R : Census V} {n : Side} {G : Gauge} {P : Rep G n}

variable (A : Bands R P)

/-- Coefficient functions assembled from an inlet on the same representation.
Zero modes don't occur in a paid inlet. Unit split remembered globally. -/
def rayPiece (x : Hot R) (j : ℕ) (U : Config G n) : ℂ :=
    if x.val=A.rays j then masked P.p.threshold (A.support j) (A.H j) U else 0

def hitPiece (x : Hot R) (i j : ℕ) (U : Config G n) : ℂ :=
    if x.val=A.marks i j then A.entries i j U else 0

def hitVolume (x : Hot R) (i : ℕ) (U : Config G n) := ∑' j,hitPiece A x i j U

def rolls (x : Hot R) : Pulse G n :=
    ((fun U => (Multi.lambda R A.units).part x.val + ∑' j, rayPiece A x j U),
      fun q U => Pack.collect P (fun i => hitVolume A x i U) q)

omit [Fintype V] in
lemma hit_legible (hA : A.Active) (x : Hot R) (i j : ℕ) :
    Legible P.p (Pack.ofAddress P.activities i) (hitPiece A x i j) := by
  unfold hitPiece
  by_cases hj : x.val=A.marks i j <;> simp only [hj,↓reduceIte]
  · exact ⟨hA.meas i j,hA.invi i j,hA.inspects i j,fun U hu => (hA.keeps i j U hu).1⟩
  exact Legible.zero ..

omit [Fintype V] in
/-- Gathering within a fixed address reads only its own support and flag
list (series identities use stronger summability separately). -/
lemma volume_legible (hA : A.Active) (x : Hot R) (i : ℕ) :
    Legible P.p (Pack.ofAddress P.activities i) (hitVolume A x i) := by
  let q := Pack.ofAddress P.activities i
  have he j := hit_legible A hA x i j
  unfold hitVolume
  refine ⟨Measurable.tsum fun j => (he j).borel,fun j U => ?_,fun U V h h' => ?_,fun U h => ?_⟩
  · exact tsum_congr fun i => (he i).symmetry j U
  · exact tsum_congr fun i => (he i).reads U V h h'
  by_contra hv; apply h
  refine (tsum_congr (g:=fun _ : ℕ => (0:ℂ)) ?_).trans tsum_zero
  intro j; by_contra he'; exact hv ((he _).inventory _ he')



omit [Fintype V] in
private lemma quiet_ne (i : R.Mode) (h : i.val.Nonempty) : R.quiet≠i :=
  fun H => nonempty_iff_ne_empty.mp h (congrArg Subtype.val H.symm)

variable {w : V → ℝ} {u c d b δ κ : ℝ} (hA : A.Active) (hR : A.Radial w u c d b) (hv : P.activities.Valid P.p δ κ)
include hR hA



include hv




end YM.AnalyticNext.GridStop.Compile
