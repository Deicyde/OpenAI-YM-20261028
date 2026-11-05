import YM.Next.FOUNDATIONS.SU2
import YM.Push.LOOP_COEFFICIENT.Block.Optimize

/-!
# Common pre-L inputs for the two possible transitions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Hist
open Matrix Set Function Filter Lattice Laurent Precision RG Wilson Exterior Bid Tree Bloch Gauge Block  Kernel
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {a : Levels G} {B : Horizon a} {P : Patch} {K : KernelChoices} {M : MapPrices}
  {F : ChartRatio G} {T : Towers P.L} {p q : Clip} {H H' : Bed} {W U : PathData G} {σ C Λ u η α Γ γ : ℝ} {j i N m : ℕ}















/-- Costs do **not** use the prices of repaired/square-root stacks,
which may be chosen at another point in the dependency order. -/
structure Realm (M : MapPrices) (B : Horizon a) : Prop where
  rows N m : m ≤ N → (B.H N m).covered (M.α (a.clock.J m)) (M.Ω (a.clock.J m))
  all N m : m ≤ N → ∀ n, Floor (B.H N m) (a.params m).clip n (M.η (a.clock.J m)) (M.Ω (a.clock.J m))
  legs N i : i < N → Craft.Donate (B.towers N i) (M.α (a.clock.J (i+1))) (M.Ω (a.clock.J (i+1))) 2
  crossings N i p : i < N → let S := a.clock.op i p; Precision.Inputs S (installed S.ratio (B.towers N i).A0) ((B.H N (i+1)).metric.acts (a.S.side (i+1) p)) ((B.H N i).metric.acts (a.S.side i p))
  top N : ∀ n, (B.H N N).diagonal.acts n=1


abbrev stageTower {L : Side} (T : Towers L) : Towers L := { T with mf := 0, mn := 0, o := 0 }



abbrev Selectors := ℕ → Clip
abbrev Cost := ℕ → ℝ

variable {s : Selectors} {χ d : Cost} {D Q drift : ℝ}

end YM.Push.Loops.Hist
