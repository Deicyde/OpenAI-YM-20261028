import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Endow
/-! # Full conditional progression: adaptive Bush to Interaction

Select course recursively, hypotheses Redometer exactly on before Crown candles.
Surviving TOP paths tied afterwards. Only ceremony hours. Do not infer these
hypotheses from Lower Wire density. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Display.Sew Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec
     Push.SectorMeasure Next.SectorChange Paint Function
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p i : ℕ} {w r l a : ℝ}
    (B : Binding C) (M : C.Makes) (J : ChartRatio G) (ξ : Purse)
local notation "Λ"=> C.path.levels
local notation "x₀"=> Atlas.clim C.path.levels k
local notation "Υ"=> C.path.levels.params k
local notation "v"=> Perch.gas ξ.era.coast
local notation "ℓ"=> C.path.levels.clock.factor (C.path.levels.clock.J k)
local notation "St"=> C.path.levels.clock.op i p
local notation "L"=> ξ.band
local notation "WL"=> Station.width C.path.levels ξ.band k
local notation "XT"=> tunnel B N i p
local notation "X"=> Atlas.clim C.path.levels i
local notation "Y"=> Atlas.clim C.path.levels (i+1)

variable (H : ShowHours J B ξ k w l r) (O : Launch C k ξ w a) (hN : k ≤ N)
    -- May require Opacity only at history-compatible and realized P
structure Redometer (p : ℕ) : Prop where
  advance i (hi : i<k) (he : Station.width C.path.levels ξ.band k≤ i) (P : Rep G (C.side (i+1) p)) (hB : Bush B (N:=N) J ξ H P hi (he.trans (Nat.le_succ i)))
     -- test on previously compatible old/red only. Not assuming a future course already PURCHASED here
      (h : ∃ Z : Course C N p k,Z.Uses (i+1) (Nat.le_trans (show i+1 ≤ k from hi) hN) P) : EpochThaw B J ξ H P hi he hB

variable (f : Course C N p k) (V : (i:ℕ)→Rep G (C.side i p))
structure Flight (i : ℕ) (h : WL ≤ i) : Prop where
  outer j (hs : i ≤ j) (he : j≤k) : Bush B J ξ (N:=N) H (V j) he (h.trans hs) ∧ f.Uses j (he.trans f.allow) (V j)
  stokes j (hp : i≤j) (he : j<k) : Stack B J ξ H he (h.trans hp) (N:=N) (V (j+1)) (V j)
  stops : Paint.survivors C N k p O.pane (V k)
lemma steadyFlow (g : Course C N p k) {j : ℕ} (he : j ≤ N) (hx : ∀ i,j< i→ i≤N → f.changeβ i=g.changeβ i) {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] (F : Config G (C.side N p)→U) : f.flow F j he=g.flow F j he:= by
  induction he using Nat.decreasingInduction with
  | self=>rw [Course.flow_self,Course.flow_self]
  | of_succ i hi ih=> rw [Course.flow_step f _ i hi,Course.flow_step g _ i hi,hx (i+1) (Nat.lt_succ_self _) hi, ih (fun j h=>hx j (lt_trans (Nat.lt_succ_self i) h))]
include M



-- actual choir & pole on this adaptive branch. Tests BEFORE any X chosen.
variable (hx : Flight B J ξ H O f V (Station.width C.path.levels ξ.band k) le_rfl)
include hx
omit M in
lemma arc_candles (i) (hb : WL≤ i) (he : i ≤ k) : Candle f i (V i) (he.trans f.allow):=by
  obtain ⟨hi,hp⟩:= hx.outer i hb he; obtain ⟨g,w,d,m,z,hV,hT⟩:=groom B J ξ O.coup hi
  exact ⟨⟨hp,w,g,m,d,z,hV,hT⟩,hi.used ▸ rfl,hi.used ▸ rfl⟩

end YM.PhysicalNext.InteractingRank
