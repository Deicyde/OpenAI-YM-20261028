import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.RESET_INCOME_PORT.Journal
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Extra.MULTISOURCE_BOUNDS.Schedule
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Consumers
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.STATIONARY_SCENES.Entrance
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Transport

set_option warningAsError false
set_option autoImplicit false
set_option synthInstance.maxSize 1024

/-!
# Counter and Prereset consumers

Value contribution at the FIRST gas, in the full-base convention. No forecast off the
subtraction paired to this very same retained path/plate. Still needs the true
Fragments production on these concrete arrays AND post-reassembly derivative/shape
control for the Income user; not another exact reset-step proof, or building actual
activities of a continuing Rep. Compare ResetIncome's Journals (`here` replaces the
HeadGas.Balance input for this use by Fragments on the priced arrays; normalizes ALL
stores, no separate flight; see `negativeLog`).
-/
noncomputable section
namespace YM.SectorTools.ActualScalar
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Input RG.Supply RG.Shoot Push.PriceCompiler
 Pressure Pressure.Testing Bid Push.SectorMeasure Precision Tree Next.SectorChange Further GaussianScalar AnalyticBridge AnalyticBridge.ResetIncome
 GaussianFieldAlignment SectorNext.Vacuum UVNext.CouplingReset
open scoped Topology Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}
section localTest
variable {c f : Side} {S : StepData c f} {e : Plate G S}
    {v : GaussianFieldAlignment.Rates} (he : Bought e v)
    (R : Rep G f) (X : ℕ → Support c) (E : ℕ → Config G c → ℝ) (m : Activities G c)
    (w : Use.Fragments R e.Flat (baseCost e R) e.book (page e he.doors) X e.point E m)
    {σ C Λ δ δ' : ℝ} (hR : R.Lawful σ C Λ δ δ') (hr : 0<R.beta)



include w hR hr



omit w hR hr in
private lemma all_good (V : Config G c) (hV : RG.flags e.point.threshold V = ∅) {p l a b}
    (hT : ReLog.Tags X e.point E p) (hF : ReLog.Fund X e.point.B l a b p) :
    ReLog.first X e.point E m V = Real.exp (-∑ i : Support c, ReLog.raw X E i V) := by
  have ht := (ReLog.intake X hT e.point.B hF).2.2.2 V Finset.univ |>.2.1
  have hx : (Finset.univ : Support c).powerset = Finset.univ := by ext; simp
  unfold ReLog.first; rw [tsum_eq_single ∅]
  · simp only [show m.gasOccurrence e.point ∅ V = 1 by simp [Activities.gasOccurrence,Activities.admissible,hV], one_mul,
      ReLog.pad,Finset.biUnion_empty, Finset.sdiff_empty,ht,hx]; congr 2; exact Finset.sum_congr rfl fun i _ => masked_eq _ _ _ _ (by simp [Healthy,hV])
  intro i hi; have hx : ¬ m.admissible e.point V i := by
    intro h; obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hi; obtain ⟨x,hx⟩ := (m.forced j).inventory_ne
    exact Finset.notMem_empty x (h.2.trans hV ▸ Finset.mem_biUnion.mpr (show ∃ j∈i, x∈(m.forced j).inventory from ⟨j,hj,hx⟩))
  simp [Activities.gasOccurrence,hx]


end localTest

/-- Pricing socket: `j.prints` for shape and output correction routing, gas JUST for
its concrete unforced atoms/reads (no use made of flight, slips, chosen), `m` also
present with its TRUE forced occurrences inside Use.Fragments.

`curse` and `Rates` remain
substantive projection/local packing obligations (at the α of this B). -/
structure Print {G : Gauge} {c f : Side} {S : StepData c f} {e : Plate G S} {v : GaussianFieldAlignment.Rates} (h : Bought e v)
    (R : Rep G f) (j : Journal e) (pred : Config G c → ℝ) (δ : ℝ) where
  m : Activities G c
  fragments : Use.Fragments R e.Flat (baseCost e R) e.book (page e h.doors) j.gas.reads e.point j.gas.atoms m
  wages : HeadGas.Token
  costs : wages.Paid j.gas
  census (P : Support c) V : Healthy e.point.threshold P V →
    HasSum (fun i => if j.origin i=P then j.glass i V else 0) (ReLog.raw j.gas.reads j.gas.atoms P V)
  curse V : RG.flags e.point.threshold V=∅ → HasSum (fun i => j.fixes i V) (pred V-e.outside R V)
  shape : ℕ → ℝ
  checks : j.Rates shape δ

namespace Print
variable {c f : Side} {S : StepData c f} {e : Plate G S} {v : GaussianFieldAlignment.Rates} {h : Bought e v}
    {R : Rep G f} {j : Journal e} {pred : Config G c → ℝ} {δ : ℝ} (Z : Print h R j pred δ)
    {σ C Λ w w' : ℝ} (hR : R.Lawful σ C Λ w w') (hr : 0<R.beta)
include Z hR hr


end Print

section launch
variable {c : Sheet G} {D : Rolls c} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Input.Directed G I Z K P) {q : ResetPrices}
    {r : Tickets} {ε g a E : ℕ → ℕ → ℝ} {s : Set ℝ} {N m p : ℕ}


end launch
end YM.SectorTools.ActualScalar
