import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Station
import YM.TraceExtension.Prom.Port.Epoch
/-!
  Variant of YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Station for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.SectorChange SectorNext.Vacuum Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Push.SectorMeasure
     YM.PhysicalNext.PhysicalGuard7f546 Curved MeasureTheory Bid Display Display.Docking Filter AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussianLaws.Local RG.Supply
open scoped Topology BigOperators Classical
variable {G : Gauge} (J : ChartRatio G) (K : MapPrices) (W : ℕ → Stage) (C : KernelChoices)
    (i j : ℕ) (ξ : Purse)

structure PostsSky (L : Side) (l d s : ℝ) : Prop where
  monitor : StorefrontSky i j C W K L ξ s G
  clamp : ∀ n : ℕ,n ≤ 2→ ∀ x ∈ Set.Icc (s/2) s, ∀ y∈ Set.Icc (s/2) s, ∀ P R : BudgetPoint, P.B=walls y → R.B=walls x → TimeBand ξ.era ξ.goal L P R x y s n
  mile : 30 ≤ ξ.horizon
  melt x : x∈ Set.Icc (s/2) s → 2*shear G L ≤ x
  wool x : x∈ Set.Icc (s/2) s → 0 ≤ K.Ω i → ∀ P : Patch,P.J=i → P.L=L → P.Branches C G → ∃ u z,∀ β β',x/2 ≤ β→ β ≤ 3*x → x/2 ≤ β' → |β'-β|≤ (W i).drift+ shear G L →
    Dawn P (initials (G:=G) K W C i j) (min (K.α i) (K.α j)) (K.η i) (max (K.Ω i) (K.Ω j)) ξ.era.coast.Q u z (ξ.sends s) x β β'
  stamp x : x∈ Set.Icc (s/2) s →∀ (c f) (S : StepData c f) (T : Tube G S), S.patch.L=L → S.patch.J=i → S.patch.Branches C G → 100*(1+radiusB (retime x)) ≤ c.val →
      (initials K W C i j).Funds S T → Boosted T (initials K W C i j) (retime x) ∧ 0<d*fiery G (retime x) L ∧ 2*(d*fiery G (retime x) L)<firstRadius G ∧
        ∀ Y : Lantern G S, Y.hood=d*fiery G (retime x) L → ∀ β : ℝ, 0<β → ∀ D : Allocation G S (retime x) l, Coupler T Y J D β

end YM.PhysicalNext.InteractingRank
