import YM.MergeProof.West.Lys
import YM.TraceExtension.Prom.Front.West.Dart
import YM.TraceExtension.Prom.Front.West.Delft
import YM.TraceExtension.Prom.Front.West.Dink
import YM.TraceExtension.Prom.Front.West.Eark
import YM.TraceExtension.Prom.Front.West.Equity
import YM.TraceExtension.Prom.Front.West.Esme
import YM.TraceExtension.Prom.Front.West.PayW
import YM.TraceExtension.Prom.Hill.Allowance
import YM.TraceExtension.Prom.Hill.Gust
import YM.TraceExtension.Prom.Hill.Incoming
import YM.TraceExtension.Prom.Hill.Pilgrim
import YM.TraceExtension.Prom.Hill.Promises
import YM.TraceExtension.Prom.Hill.Radian.Projection
import YM.TraceExtension.Prom.Hill.Ratchet
import YM.TraceExtension.Prom.Hill.Station
import YM.TraceExtension.Prom.Hill.Tuning
import YM.TraceExtension.Prom.Port.Pleas
import YM.TraceExtension.Prom.Port.Soft.Coupons
import YM.TraceExtension.Prom.Port.Soft.Grows
import YM.TraceExtension.Prom.Port.Soft.Postsale
/-!
  Variant of YM.MergeProof.West.Lys for dynamic stops. Pulse extension.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Org Input
     Display Display.Docking Filter RG.Supply Next.Rank.Station Next.Rank.Spindle Finset Bid Atlas Cells Edition Dash Spec Vac.Numbers West
     Weaver Worker Radian Tapes.West Market
open scoped Topology BigOperators Classical
variable {G : Gauge} {C : Family G} {N k p m D g u : ℕ} {w r l z : ℝ}{ξ:Purse}
    (B : Binding C) (M : C.Makes) {O : HaarBudget G} (J : ChartRatio G)
set_option quotPrecheck false
local notation "AX" => C.path.levels
local notation "α" => stamp AX N p
local notation "Y"=> clim AX k
structure LegacyCostSky (B:Binding C)(J:ChartRatio G)(w z:ℝ)(ξ:Purse)(k u D :ℕ)(O:HaarBudget G)(l r:ℝ):Prop where
    moves: LaunchSky C k ξ w z
    age : ChargeSky C.path.levels ξ.band k u O ξ.era
    hours : ShowHoursSky J B ξ k w l r
    token : VentsSky B ξ J l r k
    clears : EarkSky (prepared C.path.levels.clock.kernel) u (C.path.levels.clock.J k) D ξ.taylor ξ.band (wheelSky C.path.levels k) (clim C.path.levels k)
    room (n:ℕ)(h:n ≤ u): Caff (G:=G) ξ (clim AX k) (k-middleSky AX ξ.band k) u n
    tariff (n:ℕ)(h:n ≤ u): ∀ i,Station.widthSky AX ξ.band k ≤ i → i<k → ∀ x∈ Set.Icc ((clim AX k)/2) (clim AX k), ∀ y∈ Set.Icc ((clim AX k)/2) (clim AX k), ∀ P R : BudgetPoint,P.B=walls y → R.B=walls x→TimeBand ξ.era ξ.goal ((AX).clock.factor ((AX).clock.J (i+1))) P R x y (clim AX k) n
lemma repertoiresSky (L: LegacyCostSky B J w z ξ k u D O l r) {hN:k≤N}(he:0 ≤ ξ.band)(hp: |(C.path.rep N p k).beta-Y|≤Y/8):
    ∃ V, WhipSky B J ξ L.hours L.moves (isohypse M hN p) V (Station.widthSky AX ξ.band k) le_rfl:= by
    exact thicketSky B M J ξ L.hours L.token L.moves hN he p _ le_rfl ((Station.widerSky ..).trans (beforeSky ..)) hp
variable {K:Set (Points (m+1))}{x:Points (m+1)}{d:Fin (m+1)→ℕ}
   {P:(i:ℕ)→ Rep G (C.side i p)}
lemma y_readySky (L: LegacyCostSky B J w z ξ k u D O l r){hN:k≤N}(hf:C.ref D ≤ k)
    (V:WhipSky B J ξ L.hours L.moves (isohypse M hN p) P (Station.widthSky AX ξ.band k) le_rfl)(ht: 0 ≤ ξ.band)(hp:Ship.bank O AX (Station.widthSky AX ξ.band k))
    (hh:∀ P:BudgetPoint,P.B ≤ walls Y → Tickets P (kinetics Y))(hγ: Radian.Seal AX k p D 2 α chartHeat → Wall.Model AX D k p α)
    (hk:∀ i, C.ref (d i) ≤ k) (H:∀ i,d i ≤ D)(T:(i:Fin (m+1))→ Ribbon.StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q α)
    (v f:(i:Fin (m+1))→ C.label (d i))(hV:∀ i,Price.Solves C (mag AX ξ.band k) (d i) k N p (T i).T (v i) (f i))
    (hT:WallsSky ξ.band H v K ξ.taylor k)(hχ:tested AX ξ.band k x ∈ K)(hz:FitSky AX ξ.band k x)(hu:2 ≤ u)(hm:m+1 ≤ u)
    (hg:∀ i, ξ.cash Y*moneys C (d i) k N p (f i) ≤ Next.Rank.Perch.bill (-8) Y)(hK:∀ i,Rise.coin ((T i).W (f i)) ≤ ξ.principal Y)
    (hx:Spaced (scouts C k) (seatsSky C ξ.band x hN p) →StakeXSky m x ξ.band hN f M hk (isohypse M hN p) (Hat Y^z)):
    ∀ (s : Glyph.modes (Fin (m+1))) (_:s.val.Nonempty),
      (Ship.yardSky C ξ.band hN p).rootTest (C.beta N p) (fun U=> (Ship.invoiceSky (jointX v) (q_asked (C:=C) f) hz N p U).part s)≤ Ship.budget AX u k:= by
    let O':=isohypse M hN p; have hX:=embroideredSky B J O' ξ M L.hours L.token L.moves P V ht
    have h' := v_ceremonySky hX L.moves.coup
    have hs := (L.age.allot.permitted); have hr := L.room _ hm
    have hv:= billing_XSky B J M L.hours P L.moves V x hz hX hr hh (L.tariff _ hm)
    have hQ' : D-1 ≤ C.path.levels.clock.J k-1-2:=by have hx:=(M.stages D).1; have he:=C.path.levels.fits.mono hf; omega
    obtain ⟨he',hh⟩:= y_supplySky _ _ rfl hs hQ' L.clears N p
    let D':= hh (m+1) hm; obtain ⟨Q,hS,hA,hP⟩:= D'.optics
    obtain ⟨hx',hζ⟩:= hT.replies x hχ hz hs; let hB:= hx' p N hN
    have hO:Wall.VantageSky AX D k p (m+1) ξ.taylor ξ.band α:= ⟨hγ he',Radian.flownSky _ _ _ _ _ hS hP hA D'.visor D'.hinge D'.rotor D'.force⟩
    exact tenderlySky H v f L.age hp hm hX hz (hT.merry x hχ) h' (hζ p α hO) hv T hV
       (attireSky x f T M hk h' L.moves V.stops hr hv hu hz hB hg hK (hx hB))
end YM.PhysicalNext.InteractingRank.Soft
