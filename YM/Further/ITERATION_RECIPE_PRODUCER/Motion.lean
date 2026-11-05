import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.SOURCE_HISTORIES.Reserve
import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Levels
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry

set_option warningAsError false

/-!
# Finance some of the source-history purchases along with RLoops/RCake

Additional C given (≥1 at use), ALL before L. Like Histories.Doors
but no harder derivative-order or support purchases hidden here. Frames
and sections as in prev recipe. Higher L's fine. Will need real one-block
estimates after building unmarked history, not a scheduling consequence.
-/
noncomputable section
set_option autoImplicit false
namespace YM.Further.IterationRecipe
open Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories Motion 
open Bid Precision Next.Scheduling RG.Supply RG.Shoot  Extra.Iteration
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}







variable {s : Survey G} {K : MapPrices} {q : Quote} {v : ℕ → ℕ} {D : Rolls (s.paper q v)} {Θ : Protection D}
  {W : Supply.Delays Θ} {Y : Bar W} {I : Wait Y}
  {e : ℕ → ℕ → Exchange} {c : ℕ → ℝ} {P : Worth}

/-- Usable ALSO on any Levels and on ANY resolution on this clock;
actually paid numerically. No assumptions about `Heading` or how late N
is in the computation. `doors.rate` is the payment *target*, not proven as
a bound on the error of any actual relational comparison by L pressure.
-/
structure Cash (s : Survey G) (q : Quote) (v : ℕ → ℕ) (c : ℕ → ℝ) : Prop where
  worth j d : 1 ≤ c j → d ≤ j → (c j + 1)*orbitCost (s.B.frames.level d) ≤ q.finish.W.K j
  growth (D : Rolls (s.paper q v)) (j d : ℕ) (hd : d ≤ j) : let L := D.L j; let a := (s.melt q j).columns
    Doors.rate L * a ≤ 1 ∧ Doors.rate L * (1+a) * orbitCost (s.B.frames.level d) ≤ barunit L



lemma Cash.buys {H : History G} (h : Cash s q v c) (hc : ∀ j, 1 ≤ c j) (he : Paid I H.levels) {d m : ℕ} (hd : d ≤ H.levels.clock.J (m+1)) :
    Buys H (s.B.frames.level d) q.finish.W m (c (H.levels.clock.J (m+1))) (Doors.rate (H.S.block m)) := by
  let j := H.levels.clock.J (m+1)
  have hu := h.growth D j d hd
  have hl : H.S.block m = D.L j := Deployment.block he m
  rw [← hl] at hu
  refine ⟨hc _,(Doors.rate_pos _).le, ?_,?_⟩
  · rw [Deployment.params he]; exact hu.2
  rw [Deployment.params he]; exact (mul_le_mul_of_nonneg_right (add_le_add_right hu.1 _) (zero_le_one.trans (orbitCost_one_le _))).trans
    (h.worth j d (hc j) hd)

variable {U : Apertures} {A : ClassicalCosts} {H : QuantumCosts}






end YM.Further.IterationRecipe
