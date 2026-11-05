import YM.SectorNext.RECONNECTED_LOCALITY.Hoe
import YM.SectorNext.RECONNECTED_LOCALITY.SheetIce
import YM.SectorNext.RECONNECTED_LOCALITY.Sleet



set_option warningAsError false

/-!
# Make Cellular & Gaussian & root for exact reconnection

Don't store a sector family of independent
Z or determinant answers, and never use locality or transform of a chosen root.

Fields outside $D'$ still need a table convention satisfying these hypotheses;
Cold criterion is post-L and named once, radial rates still universal at L.

Layout for E $V,Y,S$ dependence plus precision-stencil (& `states` for hosts).

Only buying covariance ports, not asserting density formula/validity after
chart change, analytic costs on values or even numerical stencils for K etc.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect.Ice
open Words Finset Matrix Function Lattice RG Wilson Bind Window MeasureTheory
open scoped BigOperators

variable {I J ι η : Type*} {Y : η → Type*} {G : Gauge} {c : Side}
variable [Fintype I] [DecidableEq I] [∀ i,MeasurableSpace (Y i)]
variable {p : I→Site c} {q : η→Site c} {W : I→Finset I}
variable {σ k δ b ν V : ℝ} {r d t : ℕ}
variable {A : Slip G c ι Y→Matrix I I ℝ} {X : Form G c ι I Y}



/-- Group precision & appointments separately (`wired` only range & reads on
input A; prove from row stencils or slots after paying Σ/
$\mathcal P$ tests in addresses). All flags and guards to be checked at
the actual layout $X.foot$. -/
structure Aligned (X : Form G c ι I Y) (A : Slip G c ι Y → Matrix I I ℝ) (p : I→Site c) (q : η→Site c)
    (W : I→Finset I) (r d t : ℕ) (σ k δ b ν V : ℝ) : Prop where
  map : Board X p q (t+(t+d))
  row : Wired X.foot q p p r d A
  work : ∀ i,∀ j∈W i,separation (p i) (p j) ≤ t
  inlet : Eye (land p) W b
  money : ∀ s,Forecast (land p) (A s) σ δ k ν V
  cooled : cold k δ ν V b
  mirror : ∀ s,(A s).transpose=A s
  bought : ∀ s i j,Measurable (fun L : Config G c × Tables Y => A ⟨s,L.1,L.2⟩ i j)

namespace Aligned
variable (h : Aligned X A p q W r d t σ k δ b ν V)
include h








end Aligned
end YM.SectorNext.Reconnect.Ice
