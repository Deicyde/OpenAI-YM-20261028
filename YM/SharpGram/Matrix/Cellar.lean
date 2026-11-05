import YM.SharpGram.Matrix.Rainfall
import YM.UVExtension.Forest.Cave

/-!
# Leading operator for UV (analytic tuning and full mesh) family's columns

Normalized at the stipulated reference; reads actual Lacing.load via Pans
through genuine pasture, no change of cellar line. A mild strengthening of the
block minima before post-L delays, simultaneously for all the admitted
horizons, suffices to export the `barunit` price on it (note the extra factor 2
in Lacing.sailC's norm). Period and cutoff enter the height commitments, not
this price. Works even for varying offset choices within the disciplined tuning
bands; use offset zero in OPE assembly.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Function Filter Set Lattice RG RG.Supply Wilson Precision Shoot Stock Org Input Extra.Histories Source Labels
open PhysicalNext PhysicalNext.Repeat Spire Orchard Lacing Eyelet
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Mallow Lotus Legato.Bandage Lacing.RoutesF MergeProof
open Planned.GuardedAtom Guard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {hG:G.Simple} {M:Metals G} {P:Rolls M.p} {A:Alloy M P} {X:Roost.Factor A} (S: Uses X hG) (v:Keys S) {C:ℕ→ℝ} {W:Bid.Worth}(R:Legato.Bandage X C W)
    (d N m n:ℕ) (z:Rose S)
set_option quotPrecheck false
local notation "D!"=> Orchard.roof S v
local notation "H"=> Orchard.Path S v
local notation "T"=> A.B.a
local notation "F"=> (frames G).level d
local notation "π"=> localSection G d
local notation "O!"=> hol G
variable (hm:m<N)(hd:d+3≤ A.B.a.clock.J m)
local notation "g0"=> S.realBeat (v N n).val N n (m+1)
local notation "K1"=> (ray S N n m (v N n) hm).body
local notation "Υ1"=> slots1 S N m n (v N n) hm
local notation "Φ1"=> Keeper.sufficient (slots0 S N m n (v N n) hm)
local notation "V1"=> readC S R d N m n (v N n) hd
local notation "cF"=> C (A.B.a.clock.J (m+1))
open scoped BigOperators
open Motion Bid SharpGram

include hm hd
set_option maxHeartbeats 800000 in
lemma calibratedTide :
    ∃ U : Heading F,
      ThresholdDiagonal F U ((T).budget (m+1)).threshold ((T).budget m).threshold ∧
        (∀ x, (F).coeffSize (U.map x) ≤ cF * (F).coeffSize x ∧
              (F).coeffSize (U.map.symm x) ≤ cF * (F).coeffSize x) ∧
      Tips (tide S R d N m n (v N n)) ((T).S.block m) U
        (Doors.rate ((T).S.block m)) cF := by
  have hv := housed S v
  have hh : d ≤ (T).clock.J m := (le_trans (Nat.le_add_right d _) hd)
  have hC : Buys H F W m cF (Doors.rate ((T).S.block m)) := R.clock.fits H rfl m d hh
  rw [Push.PriceCompiler.block_eq A.B.valid]
  exact calibratedTips hm R.songs R.PStage R.wait (Graces.feet hd R.clock) hv R.r K1
    beam0 (ponds S N n m (v N n) hm) rfl hG R.tunes R.furthering R.corners R.shape R.clock R.stamp V1 Υ1 Φ1
    (follows S R d N m n (v N n) hm hd) hd (zero_le_one.trans hC.cost)

variable {Lu : Org.Bolt A} (a : Upland.Arc X S Lu) {t : ℕ → ℕ} (h : Lisle t A.B.a)
omit hm hd
/-- Extra O(1) in the error norm paid at the pre-block stage. -/
def ThresholdSizes (A : Levels G) : Prop := ∀ d m : ℕ, d + 3 ≤ A.clock.J m →
  Doors.rate (A.S.block m) * (1 + 2*(A.params (m+1)).columns) * orbitCost ((frames G).level d) ≤
    barunit (A.S.block m)

local notation "U0" => cellar S R a t h
local notation "L0" => Cellar.cantors v U0 d n
local notation "M0" => (L0).song N
set_option maxHeartbeats 800000 in
lemma pillarStep (hh : ThresholdSizes A.B.a) (hr : t d ≤ m) (hm : m < N) :
    CalibratedStep F H W m
      (fun x => ((Cellar.gate v (cellar S R a t h) d N n).entries (m+1) x).x)
      (fun x => ((Cellar.gate v (cellar S R a t h) d N n).entries m x).x) := by
  have hr' := hr.trans m.le_succ
  have hi := hr.trans hm.le
  have hv := (L0).lyr N hi
  let Z := hv.Vista (m+1)
  let paths := Cellar.paths S v R U0 d n
  let s := (A.B.a.params (m+1)).columns
  have hd := (h.tops d).trans ((T).fits.mono hr)
  obtain ⟨U,hU,hW,hT⟩ := calibratedTide S v R d N m n hm hd
  have hs : 0 ≤ s := zero_le_one.trans (A.B.a.params (m+1)).columns_ge
  let eta := Doors.rate ((T).S.block m)
  have he : eta * (1 + 2*s) * orbitCost (F) ≤ barunit ((T).S.block m) := hh d m hd
  have hC := R.clock.fits H rfl m d ((Nat.le_add_right d _).trans hd)
  have hC' : cF ≤ W.K ((T).clock.J (m+1)) :=
    calc (cF) ≤ (cF+eta*s) * orbitCost (F) :=
          (le_add_of_nonneg_right (mul_nonneg hC.epsilon hs)).trans
            (le_mul_of_one_le_right (add_nonneg (zero_le_one.trans hC.cost)
              (mul_nonneg hC.epsilon hs)) (orbitCost_one_le ..))
         _ ≤ _ := hC.funds
  have ht(i : Motion) : Tips (paths m N) ((T).S.block m) U eta cF := hT
  have hZ (_i : Motion) (x) : ‖Z x‖ ≤ s * (F).coeffSize ((F).core x) := by
    rw [show Z x = _ from (Lyrics.takes hv (m+1) hr' hm x)]
    exact Lyrics.climbs hv (m+1) hr' hm x
  rw [show (Cellar.gate v (cellar S R a t h) d N n).entries = _ from ((Cellar.launch v U0 d N n).choose_spec hi).2]
  refine ⟨U,hU,fun x => ⟨(hW x).1.trans ?_,(hW x).2.trans ?_⟩,fun x =>?_⟩
  · exact mul_le_mul_of_nonneg_right hC' (Work.G08.size_nonneg (F) x)
  · exact mul_le_mul_of_nonneg_right hC' (Work.G08.size_nonneg (F) x)
  let p' := ((M0).tone (m+1)).index x
  change (F).coeffSize ((((M0).tone m).plays x).x - U.leads _ (((M0).tone (m+1)).plays x).x) ≤
    barunit ((T).S.block m) * (F).coeffSize ((F).core (((M0).tone (m+1)).plays x).x)
  rw [(hv.earned.earned _ hr hm.le).currents x, (hv.earned.earned _ hr' hm).currents x,
    (hv.spaceF m hr hm x).1]
  have hh := (sailC (fun _ => paths m N) (fun _ => Z) (glaring A.B.a m n) ht hs hZ p').1
  refine hh.trans (mul_le_mul_of_nonneg_right ?_ (Work.G08.size_nonneg (F) _))
  rw [show eta + 2 * eta * s = eta * (1 + 2*s) by ring]
  exact he

lemma pillarSteps (hh : ThresholdSizes A.B.a) :
    TrueSteps (Cellar.yard v (cellar S R a t h)) W := by
  exact ⟨fun d m N n hr hm => pillarStep S v R d N m n a h hh hr hm⟩
end YM.UVExtension.Mast
