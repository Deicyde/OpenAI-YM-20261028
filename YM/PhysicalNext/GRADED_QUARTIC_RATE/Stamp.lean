import Mathlib
import YM.AnalyticNext.CUBIC_MATCH.Ledger.Figures
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Coins
import YM.AnalyticNext.QUARTIC_MATCH.Mint.Figures
import YM.Extra.ITERATION_NO_LOSS.Continuity
import YM.Extra.ITERATION_NO_LOSS.Pre
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Clock
import YM.Next.MAXWELL.Det
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.Wake
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.Lanes
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Current
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle


set_option warningAsError false
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.GradedQuartic

open Function Lattice RG RG.Supply Wilson Precision Bid Progress.StationaryScenes
open Next.Scheduling
open Extra.Iteration 
open  CubicMatch CubicMatch.Ledger
open AnalyticNext.QuarticMatch
open Hessian Tensor Joint BoxChain Mail Local Local.Rotate Local.Wages Local.Budget
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators

/-!
# Price **before** L

Use the intrinsic `meter` on the ACTUAL emitted cubic, NOT the B.fresh
fee from the sheet we're constructing now (in particular, no fee depending
on itself via the price to perform a quartic on that cubic!). Choose the
narrow-enough but positive Mint charge aperture using that emitted width
at j,i (known even for j=i), the two row widths, and Tracks. The *stage*
width can be much smaller; only the access fit on the incoming nonlinear
path widths will depend on the chosen stage width (at L selection).
-/

def feed (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (κ : KernelChoices) (j i : ℕ) :=
  max 1 (stageFee G K (d j) (d i) κ.penalty j i)

def firstFeed (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (i : ℕ) :=
  max 1 (initialBill G K (d i) i)

structure PairStamp (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (κ : KernelChoices)
    (P : Printed 3) (j i : ℕ) where
  θ : ℝ
  starts : 0<θ
  outgoingRoom : 20*boom θ ≤ (ticket G K j i).σ
  fineCurves : 20*boom θ ≤ border K j
  coarseCurves : 20*boom θ ≤ border K i
  δ : ℝ
  C : ℝ
  lands : 0<δ
  cost : 0≤C
  spends : ∀ (a : Levels G), a.clock.kernel=κ → ∀ {m N}, a.clock.J (m+1)=j →
      ∀ H : Horizon a,H.Suffices K → Progress.Joint.Swears H → Mint.AdmitsMesh a m → m<N →
        ∀ R W : PathData G, Funded H N (m+1) W → Funded H N m R → (∀ k,(R.quartic k).coeff=0) →
      ∀ {t C3 C4 : ℝ}, Led W (a.S.block m) 4 (boom θ) (border K j) (Progress.Joint.rowBill K j) C3 C4 →
        Led R 1 4 (boom θ) (border K i) (Progress.Joint.rowBill K i)
          (feed G K d κ j i*assistance (a.S.block m) C3 0) 0 →
        ∀ Y : Answer H N m W t, Mint.UpTo Y 3 R → ∃ A : rootArray G 3,
          Local.Rotate.Ink (letters P A) δ
            (C*(assistance (a.S.block m) C3 C4+assistance (a.S.block m) C3 0^2)) ∧
              Mint.UpTo Y 4 (AnalyticNext.QuarticMatch.fourth R (letters P A))

def stamp (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (κ : KernelChoices) (P : Printed 3) (j i : ℕ) :
    PairStamp G K d κ P j i := Classical.choice (by
  let t := Tracks.purchase j (K.η j) (K.α j) (K.Ω j) κ.penalty
  let s := (ticket G K j i).σ
  have ht : 0<t := Tracks.purchase_pos _ (K.eta_pos _) (K.alpha_pos _) _ κ.penalty_pos
  obtain ⟨u,hu,hα,hj,hi,hm⟩ := Mint.Affairs.narrows K j i (min s t)
    (lt_min (ticket G K j i).width ht)
  obtain ⟨hs,hv⟩ := le_min_iff.mp hm
  have he : 0 ≤ feed G K d κ j i := zero_le_one.trans (le_max_left ..)
  have hf : u ≤ t := by unfold boom at hv; linarith
  obtain ⟨δ,C,hδ,hC,H⟩ := Mint.quartic G j K κ u (Progress.Joint.rowBill K j)
    (Progress.Joint.rowBill K i) hu hα P (feed G K d κ j i) he hf
  refine ⟨u,hu,hs,by simpa only [CubicMatch.Ledger.border, min_comm] using hj,by
    simpa only [CubicMatch.Ledger.border, min_comm] using hi,δ,C,hδ,hC,?_⟩
  intro a h m N hj M hh hS hA hm R W hw hr hz t v y hy ha
  exact H _ h hj M hh hS hA hm R W hw hr hz hy ha)

structure TopStamp (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (P : Printed 3) (i : ℕ) where
  δ : ℝ
  C : ℝ
  lands : 0<δ
  cost : 0≤C
  spends : Mint.Affairs.AddOn G K i P (ticket G K i i).σ (firstFeed G K d i) δ C

def topStamp (G : Gauge) (K : MapPrices) (d : ℕ → ℝ) (P : Printed 3) (i : ℕ) :
    TopStamp G K d P i := Classical.choice (by
  obtain ⟨δ,C,hδ,hC,H⟩ := Mint.Affairs.sign4 G K i P (ticket G K i i).σ (firstFeed G K d i)
    (ticket G K i i).width
  exact ⟨δ,C,hδ,hC,H⟩)

/-- Forecast on any sheet; below buy one with exactly the Recipe pre-L choices.
`B` is for WHOLE outputs, no inherited paths here. `wake` is an extra
L-fit inequality (incoming nonlinear Access from those path budgets).
-/
structure Bespoke {G : Gauge} (S : Sheet G) (K : MapPrices) (B : ClassicalCosts) (P : Printed 3) : Prop where
  awake i : (S.profile i).width ≤ (topStamp G K (fun j => (S.profile j).clip.direct) P i).δ
  across j i : Adj j i → (S.profile i).width ≤
    (stamp G K (fun j => (S.profile j).clip.direct) S.kernel P j i).δ
  top i : (topStamp G K (fun j => (S.profile j).clip.direct) P i).C ≤ B.top i
  step j i : Adj j i →
    4*(stamp G K (fun j => (S.profile j).clip.direct) S.kernel P j i).C ≤ B.fresh j i
  wake j i (L : Side) : Adj j i → S.floorL j ≤ L.val →
    20*boom (stamp G K (fun j => (S.profile j).clip.direct) S.kernel P j i).θ ≤ (S.profile j).width*(L.val:ℝ)

end YM.PhysicalNext.GradedQuartic
