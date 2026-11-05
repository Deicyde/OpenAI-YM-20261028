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
import YM.Bid.Drops
import YM.Bid.Fuels
import YM.Org.Theatre
import YM.SectorNext.RECONNECTED_LOCALITY.Carry
import YM.SectorNext.RECONNECTED_LOCALITY.Rose
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04


set_option warningAsError false

/-!
# Open coarse-representation address types. Applying the pressure identity.

`$u$` unforced and `$d$` forced (here Font before its mask and Brand
WITH its old predicates).

Pressure exported on UNMASKED terms with the union mask, ready
for corrective attachment.

Every choice label with its full halo, even those multiplying
zero.

The Anchor for incoming u norm needn't itself be signed covariant (prior to building
output Activities); support & the formulas here retain THEIR actual moves.

Use for physical
configurations & genuine BudgetPoint (before the projection-vanishing gates for regular E).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Reconnect

open RG Lattice Filter Function Wilson MeasureTheory Rose Words Ledger
open scoped Matrix.Norms.Frobenius Classical

variable {G : Gauge} {c : Side} {ι β : Type*}

structure Font (G : Gauge) (c : Side) (ι : Type*) where
  range : ι → Support c
  active i : (range i).Nonempty
  dial : ι → Config G c → ℝ

namespace Font
variable (P : BudgetPoint) (U : Font G c ι)



/-- At a stage threshold P, want each u activity smooth, with hit budget on
actual support and one designated anchor (e.g. projection), and family symmetry.
Anchors here used only for quantitative tests, not compulsory label metadata.
-/
structure Names (f : ι → ℝ) : Prop where
  regular i : P.Regular (U.range i) (U.dial i)
  powers i : ∃ o∈U.range i,P.supBounds o (U.range i) (U.dial i) (f i)
  moves (s : Signed) (b : Site c) : ∃ p : Equiv.Perm ι, carrying p (sitePerm s b) U.range U.range ∧
    ∀ i V,U.dial (p i) V=U.dial i (pull s b V)

variable {U P}


variable (U)








variable {U}



namespace Names
variable {f : ι → ℝ} (h : U.Names P f)
include h






end Names









end Font

structure Brand (G : Gauge) (c : Side) (ι : Type*) where
  forced : ι → ForcedAddress G c
  ink : ι → Config G c → ℝ

namespace Brand
variable (D : Brand G c ι)

abbrev range (i : ι) := (D.forced i).support
abbrev require (i : ι) := (D.forced i).inventory

structure Plan (s : Signed) (b : Site c) where
  sends : Equiv.Perm ι
  support : carrying sends (sitePerm s b) D.range D.range
  primary : carrying sends (sitePerm s b) D.require D.require
  test i V : (D.forced (sends i)).extraTest V ↔ (D.forced i).extraTest (pull s b V)
  payload i V : D.ink (sends i) V=D.ink i (pull s b V)

structure Names (P : BudgetPoint) : Prop where
  gauge i : GaugeInvariant (D.ink i)
  gaugeTest i k U : (D.forced i).extraTest (Lattice.gauge k U) ↔ (D.forced i).extraTest U
  measures i : Measurable (D.ink i)
  events i : MeasurableSet {x | (D.forced i).extraTest x}
  localizes i : UsesFinal P.threshold (D.range i) (D.ink i)
  tested i : UsesFinal P.threshold (D.range i) (D.forced i).extraTest
  renames s b : Nonempty (D.Plan s b)
  permits i V : D.ink i V ≠ 0 → (D.forced i).eligible P.threshold V

def covered (P : BudgetPoint) (V : Config G c) (b : Finset ι) := (b:Set ι).PairwiseDisjoint D.range ∧
    b.biUnion D.require=flags P.threshold V

def record (P : BudgetPoint) (V : Config G c) (b : Finset ι) :=
    if D.covered P V b then ∏ i∈b,D.ink i V else 0

/-- Value budgets (output derivative only on regular, not on these). Exponent may
be a reserve a different from P when propagating through attachments at this scale. -/
def Charged (P : BudgetPoint) (a ε : ℝ) := ∃ v : ι → ℝ, (∀ i V, |D.ink i V| ≤ v i) ∧ Ac.Hit D.range P.B v a ε

lemma active (i : ι) : (D.range i).Nonempty := (D.forced i).inventory_ne.mono (D.forced i).inventory_sup

theorem liable {P : BudgetPoint} {a ε : ℝ} (H : D.Charged P a ε) (ha : 0 ≤ a) : Dominated (fun b (x : Config G c) => D.record P x b) := by
  obtain ⟨v,hv,h⟩:=H
  have he i := (abs_nonneg (D.ink i 1)).trans (hv i 1)
  have hp: Summable v:=(Ledger.volume ha he h (fun i _ => D.active i)).2.1
  refine ⟨fun b => ∏ i∈b,v i,summable_finsetProd_of_summable_norm hp.norm,fun b x => ?_⟩
  unfold record; simp only; split
  · rw [norm_prod]; exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => hv i x
  rw [norm_zero]; exact Finset.prod_nonneg fun _ _ => he _
end Brand



end YM.SectorNext.Reconnect
