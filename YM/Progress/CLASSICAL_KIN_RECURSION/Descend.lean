import YM.Next.SCHEDULE.Continuing
import YM.Next.SCHEDULE.Dues
import YM.Progress.CLASSICAL_KIN_RECURSION.Row


set_option warningAsError false

/-!
# One *branch* over each cutoff, not one path-existence theorem used
at all levels independently

`assemble` is a constructor lemma. Separate mathematical task here to prove
its hypotheses (peak readiness, scene calls and emissions) – these themselves
are NOT appropriate external assumptions for the classical task. Space for
arbitrary admissible paid regions (numerical Levels), use common alpha/stamp
slots but here alpha is padding. `Blueprint` deliberately omits the two
quantum estimate fields of `Kin.Planned`. Every actual P below uses the given
period, **every** forest on its ratio, the same path W and its metric.
-/
set_option autoImplicit false
noncomputable section
open Filter Function Set
namespace YM.Progress.ClassicalKin
open Lattice RG Wilson Precision Tree Exterior Bloch Laurent Bid RG.Supply Next.Scheduling
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {a : Levels G} {C : Horizon a} {O : ChartRatio G}
  {s : Sheet G} {D : Rolls s}

def Summit (a : Levels G) (N : ℕ) (W : PathData G) := ∀ p : ℕ, ∀ j : ℕ,j ≤ 4 →
    SameJet j (fun x => mainTerm (a.params N).clip W (represent (x:Dir G (a.S.side N p))))
      (fun x => Wilson.energy (represent x))

abbrev Governors (a : Levels G) (m : ℕ) := ∀ p : ℕ, ∀ F : Forest (a.clock.op m p).ratio,
    fieldDir G (a.S.side m p) 1 → AxisChart G F

def Houses (C : Horizon a) (Q : PostCost D) (N m : ℕ) (W : PathData G) (r : Governors a m) :=
    ∀ p : ℕ, ∀ F : Forest (a.clock.op m p).ratio,
      let c := (a.params (m+1)).clip
      PriceGap F c W (Q.η (a.clock.J (m+1))) ∧ Critical F c W (r p F) ∧
        Guessed F (installed (a.clock.op m p).ratio (C.towers N m).A0) (r p F) ∧ HeatG F c W (r p F) (C.H N m)

def Sends (a : Levels G) (m : ℕ) (W T : PathData G) (r : Governors a m) :=
    ∀ p : ℕ, ∀ F : Forest (a.clock.op m p).ratio,
      ClassicalMatch F (a.params (m+1)).clip (a.params m).clip W T (r p F)

/-- Inherited row is identified exactly (independent additional width via
`Horizon.Suffices`), and `emitted` is in the width paid *also* when the
next call uses the same smoothing stage. All loop slots `blank` here.
-/
structure Escrow (C : Horizon a) (b : Strips) (k : Figures) (N m : ℕ) (W : PathData G) : Prop where
  exact_row : W.row=coreRow (C.H N m)
  empty_loop : W.loop=blank G 2
  funds : W.Bounds (a.params m).clip (a.params m).width (a.params m).paths 0
  emitted :
    let j := a.clock.J (m+1); let i := a.clock.J m
    if N=m then W.Bounds (a.params m).clip (b.launch i) (k.beginCost i) 0 else
      W.Bounds (a.params m).clip (b.emits j i)
        (classicalFee (a.S.block m).val (k.classic j i) (a.params (m+1)).paths) 0

variable {b : Strips} {k : Figures}

structure Blueprint (M : Kin C O) (Q : PostCost D) : Prop where
  stage : s.profile = a.clock.stage
  lengths : D.L=a.clock.factor
  links N m : m ≤ N → Attached (C.H N m) (M.path N m)
  cap N m : m ≤ N → (M.path N m).Bounds (a.params m).clip (a.params m).width (a.params m).paths (a.clock.loopCap m)
  peak N : Summit a N (M.path N N)
  initial N l : ((M.path N N).loop l).coeff=0
  heart N m : m < N → Houses C Q N m (M.path N (m+1)) (M.stationary N m)
  parts N m : m < N → Sends a m (M.path N (m+1)) (M.path N m) (M.stationary N m)

variable {M : Kin C O} {Q : PostCost D}
structure Progeny (M : Kin C O) (Q : PostCost D) (b : Strips) (k : Figures) : Prop extends Blueprint M Q where
  reserves : ∀ N m,m ≤ N → Escrow C b k N m (M.path N m)

namespace Escrow
variable {N m : ℕ} {T : PathData G} (h : Escrow C b k N m T)
include h




end Escrow


end YM.Progress.ClassicalKin
