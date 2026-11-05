import YM.AnalyticBridge.SECTOR_MARKED_IDENTITY.Shared
import YM.PhysicalNext.UNMASKED_THROUGH_LAUNCH.Merchant
import YM.Planned.ATOM_GUARDED_LAYOUT.Guards

/-!
# `Pose` variant

This recipe specifies exact layout at top and mandates Keeper and positivity.
`Opening`, next-level funds `NextBook` to use even with SectorChange/Bought.
Continuation through these particular retain tests still not shown. Contrast
with the SERVICE variant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.ThroughLaunch
open Function Filter Set Lattice RG Source Wilson Precision RG.Supply Input
open WilsonStartup Further.StrongStartup Extra.Histories Next.Foundations Pressure Testing Org
open Planned.GuardedAtom.Guard RG.Shoot Next.SectorChange Push.SectorMeasure
open scoped Topology BigOperators Matrix.Norms.Frobenius

variable {G : Gauge} {O T : MapPrices} {K : Tariffs} {P : Sheet G}
variable {m v : ℕ → ℕ} {D : Rolls (ThroughLaunch.raise P m)} {Q : PostCost D}
  {Z : Protection D} {W : Delays Z} {Y : Bar W} {I : Wait Y}
variable {a : Levels G} {l : ℕ → ℝ} {U : Horizon a} {w : Kin U (chart G)}

section gates
-- Illustrate noncircular inputs to a future `Advance`-phase step.

def pose (F : Builder.Gates a) : Builder.Gates a := {F with
    retain := fun N i p u => F.retain N i p u ∧ (∀ _h : i=N, u=(Start.layout a i p u.beta)) ∧
      (∃ k : Keeper u.p u.activities, ∀ j, u.activities.K (k.code j)=0) ∧
      ∀ V,0 < u.eval V }


/-- Passage to the real sector calculation. Pinned to SAME query/sheet;
produces permission for all active bundles (and actual Nonempty Allocation,
so can take it on any input). No claim of independent-sector measure phenomena.
Already includes for top band all β and p without Advance hypothesis. -/
structure NextBook {M : Metals G} {D : Rolls M.p} (A : Alloy M D) (f y : ℕ → ℕ → ℝ) : Prop where
  funds N i (t : Side) : i<N → Bid.Sworn (A.B.M.H N i) t G
  next (N i p : ℕ) : i < N →
    let S := A.B.a.clock.op i p; let U := Testing.ships A.B N i p; let x := A.B.a.clock.hatBeta i
    let j := A.B.a.clock.J (i+1); let h := A.B.a.clock.J i
    let W := f j h; let d := y j h * A.B.a.clock.threshold (i+1)
    Bid.Larger (G:=G) S ∧ Nonempty (Allocation G S x W) ∧ ∀ (Y : Rep G _), Lives A.B.bake N (i+1) p Y →
      Y.beta∈band A.B.a (i+1) →
      (∀ q, 0 < Y.eval q) ∧ (∃ k : Keeper Y.p Y.activities, ∀ s,Y.activities.K (k.code s)=0) ∧
        (i+1=N → Y=Start.layout A.B.a (i+1) p Y.beta) ∧ 0<W ∧
        (∃ κ : ℝ, 0<κ ∧ PointCharge U x W κ) ∧
          ∀ (H : Allocation G S x W) (F : Tree.Forest S.ratio) (ρ : Chi), Marked.Bought U x Y F H ρ M.O d



end gates


end YM.PhysicalNext.ThroughLaunch
