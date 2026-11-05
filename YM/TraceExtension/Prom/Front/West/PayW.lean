import YM.MergeProof.West.PayW
import YM.TraceExtension.Prom.Front.West.AudienceM
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Horns
import YM.TraceExtension.Prom.Front.West.Muse
import YM.TraceExtension.Prom.Front.West.Throne
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Cadence
import YM.TraceExtension.Prom.Hill.Flux.Conductor
import YM.TraceExtension.Prom.Hill.LedgerGate
import YM.TraceExtension.Prom.Hill.Memorandum
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.ShapeS
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Bonfire
import YM.TraceExtension.Prom.Port.Soft.Coupons
import YM.TraceExtension.Prom.Port.Soft.Crowns
import YM.TraceExtension.Prom.Port.Soft.Grows
import YM.TraceExtension.Prom.Port.Soft.Spear
import YM.TraceExtension.Prom.Port.Soft.Unlid
import YM.TraceExtension.Prom.Port.Stagecraft
/-!
  Variant of YM.MergeProof.West.PayW for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Display Display.Docking Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
    RankCovariance Next.Rank Tapes Perch Paint Spindle Station Peak Ac Thirst Glyph Atlas Value Flux Marker Rise Normal Ribbon Spindle Glyph Exponential Camp Cells Edition Relation EntryWord Alarm Corona Tapes.West
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {C : Family G} {N i p k n u : ℕ} {w r l a : ℝ} {ξ:Purse}{X R P} {c:Course C N p k}
lemma v_ceremonySky (H:NylonSky c P X R ξ)(ht:CorridorSky C.path.levels ξ.band ξ k): Tapes.West.CeremonySky ξ c P R X:= by
   refine ⟨ht,H.paths,H.probes,fun i hi hh => ⟨(H.fixture hi hh).budget, (H.fixture hi hh).threshold,Novice.small _ (H.fixture hi hh)⟩,H.invariant⟩

section
local notation "St" => C.path.levels.clock.op i p
local notation "D" => C.path.levels

variable (B : Binding C) (J:ChartRatio G) (m:C.Makes)
variable (H:ShowHoursSky J B ξ k w l r)(V : (i:ℕ)→ Rep G (C.side i p))(O:LaunchSky C k ξ w a) (hv : WhipSky B J ξ H O c V (Station.widthSky C.path.levels ξ.band k) le_rfl)
include B H V O hv m
lemma billing_XSky (Y:Points n)(hy: FitSky C.path.levels ξ.band k Y)
    (he:NylonSky c V X (short B N p) ξ)
    (hx:Caff (G:=G) ξ (clim C.path.levels k) (k-middleSky C.path.levels ξ.band k) u n)
    (ht:∀ P : BudgetPoint,P.B≤walls (clim C.path.levels k)→Tickets P (kinetics (clim C.path.levels k)))
    (hs:∀ i,Station.widthSky C.path.levels ξ.band k ≤ i → i<k → ∀ x∈ Set.Icc ((clim C.path.levels k)/2) (clim C.path.levels k), ∀ y∈ Set.Icc ((clim C.path.levels k)/2) (clim C.path.levels k), ∀ P R : BudgetPoint,P.B=walls y → R.B=walls x→TimeBand ξ.era ξ.goal (C.path.levels.clock.factor (C.path.levels.clock.J (i+1))) P R x y (clim C.path.levels k) n) : PlesseySky ξ Y c V (short B N p) u:=by
  have hs (i) (hi : Station.widthSky D ξ.band k ≤ i) (hx : i<k) : TimeBand ξ.era ξ.goal (C.path.levels.clock.op i p).patch.L (V (i+1)).p (V i).p (clim C.path.levels i) (clim C.path.levels (i+1)) (clim C.path.levels k) n:= by
    have hf: Station.widthSky C.path.levels ξ.band k ≤ i+1:= hi.trans (Nat.le_succ _)
    rw [(sizes_atSky ξ O.coup hi hx p).1]; exact hs i hi hx _ (O.coup.court _ hi hx.le) _ (O.coup.court _ hf hx) _ _ (he.use_ _ hf hx).budget (he.use_ _ hi hx.le).budget
  have hQ i (h : Station.widthSky D ξ.band k ≤ i) (hg : i≤k) := ht (V i).p (show (V i).p.B≤_ by
    have hh : 1 ≤ clim D i:= ((D).fits.delayed _).le; rw [(he.use_ i h hg).budget]; exact wall_mono hh ((D).fits.delayed k|>.le) (O.coup.court i h hg|>.2))
  constructor
  · intro i hi hj; dsimp only; obtain ⟨b,z,h⟩:= allocSky V hv hi hj
    have hL:= (Station.widerSky ..).trans hj
    obtain ⟨hp,T,A,Z,hV,hW⟩:= (hv.stokes i hL hi).heats
    obtain ⟨q,hq⟩:= galaFtSky h m (hv.outer _ (hL.trans (Nat.le_succ i)) hi).1.pets J A Z T (hs i hL hi) O.coup.heft hx.horizon Y hy _ (show 0<loot ξ (clim C.path.levels k) u from Real.exp_pos _) hV (hW _ (Real.exp_pos _)).1
    exact ⟨h.a_pprove m Y A,tapsFtSky (S:=ξ.era) (h.a_pprove m Y A) q O.coup.heft he.paths.canvas hy (he.fixture hj hi.le).budget (Real.exp_pos _) (hQ i hL hi.le) hq⟩
  intro i hp hj; have h:i<k:= lt_of_lt_of_le hj (beforeSky ..)
  obtain ⟨hu,T,A,Z,hV,hW⟩:=(hv.stokes i hp h).heats
  obtain ⟨hx,hR⟩:= hv.outer (i+1) (hp.trans (Nat.le_succ i)) h
  obtain ⟨q,Hq⟩:= shutters_Sky h hx.pets hR.coupling A Z T (hs i hp h) hp Y hy (Ship.allowance D u k) (Real.exp_pos _) hV (hW _ (Real.exp_pos _)).2
  exact Flux.tappedSky _ _ _ (hQ i hp h.le) Hq (Real.exp_pos _)
end
end YM.PhysicalNext.InteractingRank.Soft
