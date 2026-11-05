import YM.MergeProof.West.Delft
import YM.MergeProof.West.Eark
import YM.MergeProof.West.Esme
import YM.MergeProof.West.PayW
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Tally
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Spinto
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.Money
import YM.PhysicalNext.INTERPOLATED_SECANTS_FC.Tariff


/-!
# Retain many-marker comparison witness per post at any later p
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
structure LegacyCost (B:Binding C)(J:ChartRatio G)(w z:ℝ)(ξ:Purse)(k u D :ℕ)(O:HaarBudget G)(l r:ℝ):Prop where
    moves: Launch C k ξ w z
    age : Charge C.path.levels ξ.band k u O ξ.era
    hours : ShowHours J B ξ k w l r
    token : Vents B ξ J l r k
    clears : Eark (prepared C.path.levels.clock.kernel) u (C.path.levels.clock.J k) D ξ.taylor ξ.band (wheel C.path.levels k) (clim C.path.levels k)
    room (n:ℕ)(h:n ≤ u): Caff (G:=G) ξ (clim AX k) (k-middle AX ξ.band k) u n
    tariff (n:ℕ)(h:n ≤ u): ∀ x∈ Set.Icc ((clim AX k)/2) (clim AX k), ∀ y∈ Set.Icc ((clim AX k)/2) (clim AX k), ∀ P R : BudgetPoint,P.B=walls y → R.B=walls x→TimeBand ξ.era ξ.goal ((AX).clock.factor ((AX).clock.J k)) P R x y (clim AX k) n
lemma repertoires (L: LegacyCost B J w z ξ k u D O l r) {hN:k≤N}(he:0 ≤ ξ.band)(hp: |(C.path.rep N p k).beta-Y|≤Y/8):
    ∃ V, Whip B J ξ L.hours L.moves (isohypse M hN p) V (Station.width AX ξ.band k) le_rfl:= by
    exact thicket B M J ξ L.hours L.token L.moves hN he p _ le_rfl ((Station.wider ..).trans (before ..)) hp
variable {K:Set (Points (m+1))}{x:Points (m+1)}{d:Fin (m+1)→ℕ}
   {P:(i:ℕ)→ Rep G (C.side i p)}
lemma y_ready (L: LegacyCost B J w z ξ k u D O l r){hN:k≤N}(hf:C.ref D ≤ k)
    (V:Whip B J ξ L.hours L.moves (isohypse M hN p) P (Station.width AX ξ.band k) le_rfl)(ht: 0 ≤ ξ.band)(hp:Ship.bank O AX (Station.width AX ξ.band k))
    (hh:∀ P:BudgetPoint,P.B ≤ walls Y → Tickets P (kinetics Y))(hγ: Radian.Seal AX k p D 2 α chartHeat → Wall.Model AX D k p α)
    (hk:∀ i, C.ref (d i) ≤ k) (H:∀ i,d i ≤ D)(T:(i:Fin (m+1))→ Ribbon.StampDuty C k N p (d i) ξ.taylor (P k) ξ.era.coast.Q α)
    (v f:(i:Fin (m+1))→ C.label (d i))(hV:∀ i,Price.Solves C (mag AX ξ.band k) (d i) k N p (T i).T (v i) (f i))
    (hT:Walls ξ.band H v K ξ.taylor k)(hχ:tested AX ξ.band k x ∈ K)(hz:Fit AX ξ.band k x)(hu:2 ≤ u)(hm:m+1 ≤ u)
    (hg:∀ i, ξ.cash Y*moneys C (d i) k N p (f i) ≤ Next.Rank.Perch.bill (-8) Y)(hK:∀ i,Rise.coin ((T i).W (f i)) ≤ ξ.principal Y)
    (hx:Spaced (scouts C k) (seats C ξ.band x hN p) →StakeX m x ξ.band hN f M hk (isohypse M hN p) (Hat Y^z)):
    ∀ (s : Glyph.modes (Fin (m+1))) (_:s.val.Nonempty),
      (Ship.yard C ξ.band hN p).rootTest (C.beta N p) (fun U=> (Ship.invoice (jointX v) (q_asked (C:=C) f) hz N p U).part s)≤ Ship.budget AX u k:= by
    let O':=isohypse M hN p; have hX:=embroidered B J O' ξ M L.hours L.token L.moves P V ht
    have h' := v_ceremony hX L.moves.coup
    have hs := (L.age.allot.permitted); have hr := L.room _ hm
    have hv:= billing_X B J M L.hours P L.moves V x hz hX hr hh (L.tariff _ hm)
    have hQ' : D-1 ≤ C.path.levels.clock.J k-2:=by have hx:=(M.stages D).1; have he:=C.path.levels.fits.mono hf; omega
    obtain ⟨he',hh⟩:= y_supply _ _ rfl hs hQ' L.clears N p
    let D':= hh (m+1) hm; obtain ⟨Q,hS,hA,hP⟩:= D'.optics
    obtain ⟨hx',hζ⟩:= hT.replies x hχ hz hs; let hB:= hx' p N hN
    have hO:Wall.Vantage AX D k p (m+1) ξ.taylor ξ.band α:= ⟨hγ he',Radian.flown _ _ _ _ _ hS hP hA D'.visor D'.hinge D'.rotor D'.force⟩
    exact tenderly H v f L.age hp hm hX hz (hT.merry x hχ) h' (hζ p α hO) hv T hV
       (attire x f T M hk h' L.moves V.stops hr hv hu hz hB hg hK (hx hB))
end YM.PhysicalNext.InteractingRank.Soft
