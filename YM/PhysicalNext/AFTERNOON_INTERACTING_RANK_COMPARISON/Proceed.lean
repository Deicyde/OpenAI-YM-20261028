import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.Extra.MULTISOURCE_BOUNDS.Merger
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Tern
import YM.PhysicalNext.GRADED_QUARTIC_RATE.Stamp
import YM.PhysicalNext.SAME_SERVICE_FRESH_DETERMINANT.Orders
import YM.Planned.RECIPE_STARTUP_PORT.Horizon
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOOP_COEFFICIENT.Frame.Atlas
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Matching
import YM.Push.STRESS_FLUX.Ward
import YM.UVNext.COUPLING_RESET.Reset


/-!
# Exact handoff to an incumbent Family.

Only at Tops with purchased Candle and paths, on one purchased Course.

Includes actual polls through all spectators bound by this X from the start.

Other families untouched.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec OS Extraction OS.Ground Analysis Tree Laurent Bloch Exterior FreeResolvent
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) {O : HaarBudget G} (J : ChartRatio G) {d : ℕ}
    {ξ : Purse}
local notation "Y" => C.path.levels
local notation "xK" => Atlas.clim C.path.levels k
section
structure Candidate (g : Launch C k ξ w a) (V : (u : ℕ)→ Rep G (C.side u p)) (hN : k≤N) : Prop where
  home : Paint.survivors C N k p g.pane (V k)
  fund : ∀ i, Station.width C.path.levels ξ.band k≤ i →∀ h : i≤k,Candle (keeping M p N k hN) i (V i) (h.trans hN)
  follows : ∀ i,Station.width C.path.levels ξ.band k ≤ i → i≤k → (V i).path=(C.path.rep N p i).path ∧ (V i).clip=(C.path.rep N p i).clip

include M in
lemma port_candles {V : (i : ℕ)→ Rep G (C.side i p)}  {h : k ≤ N} (hp : ∀ i,Station.width C.path.levels ξ.band k ≤ i → i≤k → (V i).path=(C.path.rep N p i).path ∧ (V i).clip=(C.path.rep N p i).clip)
    (i : ℕ) (ht : Station.width C.path.levels ξ.band k ≤ i) (hm : i<k) (F : Forest (C.path.levels.clock.op i p).ratio) :
    let V':= V (i+1)
    let S:= C.path.levels.clock.op i p
    Attached (B.world.H N (i+1)) V'.path ∧
      (∀ t:S.Choices, Precision.hessian F t V'.clip V'.path 0 0=treeMatrix G S F (B.world.H N (i+1)).metric ∧
          Affine.primary S F t V'.clip V'.path (fun _=>true) 0=treeMatrix G S F (B.world.H N (i+1)).metric) ∧
      Normal.scope stem (flatLinks B.pays (lt_of_lt_of_le hm h) F)=(track (stamp C.path.levels N p) i).Q ∧
      ∀ v x, froth (flatColumn B.world N i p F v) x = Complex.re (Normal.reads ((stamp C.path.levels N p).path i) (fun j=> (froth v j:ℂ)) x):= by
  intro V' S
  obtain ⟨hx,hV⟩:= hp (i+1) (ht.trans (Nat.le_succ i)) hm; unfold V';rw [hx,hV]
  exact ⟨B.paths N (i+1) (lt_of_lt_of_le hm h) p,(RankCovariance.uncut M B) N i p (lt_of_lt_of_le hm h) F⟩


end

-- Keep original-phase poses exactly in place, even if future course changed
lemma marking (M : C.Makes) {d m} (hp : C.ref d ≤ k) (g f : Course C N p k) (X : Points (m+1)) (b : ℝ) (F : Fin (m+1)→C.label d) (s : ℝ): Stake m X b g.allow F M hp g s ↔ Stake m X b f.allow F M hp f s:= by
  unfold Stake Edition.Bills; dsimp only
  rw [steadyFlow g f (he:=g.allow) (fun i hi hj=> (g.same i hi.le hj).trans (f.same i hi.le hj).symm)]

-- exercise to exact physical call on connection weights in Atlas.
-- Given single mixed original-phase input Stake, PRICE AND BOOT.


-- Exact consumer.
-- higher-color multi-source step estimates (Stake). Only when paid inside.
variable (F : Cohesion C d) {S : Table C.book} (X : Columns C S d)
local notation "Q"=> F.current k
-- require full array. Named also for exact Unmark update.
def LanternMarks (k : ℕ) := ∀ (hk : C.ref d ≤ k), (∀ i,Fit Y (F.current k).band k (X.row i).expected) →
    ∀ᶠ N in atTop, ∀ hN : k≤N,∀ p : ℕ, ∀ i, ∀ p' : Fin ((X.row i).extra+1)→ C.label d,
      (∀ j,bill F.pan (clim Y k)*moneys C d k N p (p' j)≤ bill (-8) (clim Y k)) →
        Stake (X.row i).extra (X.row i).expected (F.current k).band hN p' M hk (keeping M p N k hN) (YM.Vac.Numbers.Hat (clim Y k)^F.mark)

structure Globes (Z : ShowHours J B (F.current k) k w l r) : Prop where
  receives (hk : C.ref d≤ k) (hX : ∀ i,Fit Y (F.current k).band k (X.row i).expected):
    ∀ᶠ N in atTop,∃ hN : k≤N,∀ p : ℕ, Redometer B J (F.current k) Z hN p



-- joint successor. Use transported laps. Even for ALL financed d arcs.
-- 'Y .../ ...' for the same panel d from the paid chapter. Consume true after node. No rank inference without demands preserved.

end YM.PhysicalNext.InteractingRank
