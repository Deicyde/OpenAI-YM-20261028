import YM.FullVolume.Orbit.Stardust

/-!
 # Physical one-step laws on comparison inputs, before projecting K

 `spatial A` cannot be used to advance the Wilson history; it accepts a broader class of
 test inputs on the **same** paths/clips/budgets. `savory` gives membership of the output on
 these. We check here that even in this broader scope the `Chord` being used for E,K and
 beta local estimates is taking the actual RG step. No positivity of arbitrary input or output
 asserted; importantly no assumption of no flags. Also expose the compulsory-activity reserve.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.ClearanceR
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision
open SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing
open PriceCompiler Opera
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork Roof Daisy Charity
open Rain Roost Lotus Mallow Marlin Trio
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {X : Metals G} {D : Rolls X.p} {A : Alloy X D} {R : Factor A}
    {N m n : ℕ} {c c₁ : ℝ} (H : Chord R N m n c c₁) (Y : Chord.Flight A N m n)
set_option quotPrecheck false
local notation "Hm" => H.moment Y
local notation "B" => A.B.a.budget m
local notation "W" => A.B.kin.path N m
local notation "S" => A.B.a.clock.op m n
local notation "α" => A.B.kin.alpha N m

-- Extend Rain.sprint in precisely this use to spatially admissible inputs. Keep the actual
-- pre-assembly reservation (same funding ordinal, permits and dictionary). This is unmarked;
-- it does not allow replacing a single marker in a different polynomial representation.
set_option maxHeartbeats 800000 in
lemma postingTrial : ∃ τ, (A.B.a.clock.op m n).push Y.val.beta Y.val.eval =
    earlyValue (H.listing Y) W (A.B.a.params m).clip (B) (H.source Y) Y.val.beta τ α := by
  let F : ℝ → Rep G (A.B.a.S.side (m+1) n) := fun _ => Y.val
  have hF (x) (_ : x ∈ Set.Icc (0 : ℝ) 0) : Lives (Roof.spatial A).bake N (m+1) n (F x) ∧
      (F x).beta ∈ band A.B.a (m+1) := Y.property
  have hx : (0 : ℝ) ∈ Set.Icc (0:ℝ) 0 := Set.left_mem_Icc.mpr le_rfl
  have hv : Curve (A.B.a.budget (m+1)) F (Set.Icc 0 0) := by
    rw [← Y.property.1.point]; exact Rain.unchanged ..
  obtain ⟨U,-⟩ := verdict H.earns H.paid hv hF hx
  let d := H.order (Rain.listIn (F 0))
  have hk := ((H.city (Rain.listIn (F 0))).emits F U hv hF rfl 0 hx).1
  obtain ⟨hX,hL,-⟩ := H.at_turn U hx hv hF
  change H.listing Y = _ at hX
  change H.source Y = _ at hL
  let t := U.latch 0
  let M : Return.Wood A.B m n := Classical.choice (Tree.select (S).ratio (S).patch.odd_side)
  let Yd := H.tone.offers d (Rain.minute U hF 0)
  let k := Rain.lint R.target A m
  let e := Trio.base k (radiusB (A.B.a.clock.hatBeta m))
  let V := U.sister t
  have ht := (Roof.coating R.pledging.conducts H.paid (fun x hx => (hF x hx).2)).decent
  have he := Boulevard.lays R.shape A (A.B.a.S.oneStep m n).exact_size V R.inn.chip H.paid
      R.pledging.jewels R.pledging.conducts.full (R.pledging.agenda _ _ (step_paid A.B.a m)|>.1) ht
      (U.honors t) M
  let q := stanzaFee U d M 0
  refine ⟨q,?_⟩
  rw [hX, hL]; funext i
  apply Eq.trans (he.2 i)
  have hi := Marlin.carries (B) U.doors e (2*e) (uptick U d 0) (beams U hF H.tone d 0)
    (Rain.nights U hF H.tone d 0) i (R:=posting (B) U.base) (U.fullSong 0) (fun _=>⟨rfl,rfl⟩)
    W (A.B.a.params m).clip Y.val.beta (U.payment M 0) α (Meadow.barony _ Chi.canonical d α 0 1)
    (lavish R.pledging H.paid U hv hF R.inn (R.settles _ _) H.tone d 0 hx) hk
    (fun i=> Trio.levy (B) V α d (screens R.target A m) e Yd i _ _ he.1)
    (fun s b=> Song.motion (B) U.base V Chi.canonical α s b)
    (fun s b=> Beam.moves U.base (B) Chi.canonical V s b _)
  exact hi

set_option maxHeartbeats 600000 in
/-- One unmarked step, also on the spatial comparison class (no PeriodFuture, not a Move).

 The K price on the right is potentially stronger than `forcedAllowance`; the conversion to a
 small price in divided `Home` norm will use schedule payment. -/
theorem trial (g : G.Simple) : (H.moment Y).eval =
      (A.B.a.clock.op m n).push Y.val.beta Y.val.eval ∧
    (H.moment Y).activities.KBound (B) (Return.forcing A.B m) := by
  let F : ℝ → Rep G (A.B.a.S.side (m+1) n) := fun _ => Y.val
  have hb := Roof.coating H.earns.conducts H.paid (R:=F) (s:=Set.univ) (fun x _=>Y.property.2)
  have hX (x : ℝ) (_ : x ∈ (Set.univ : Set ℝ)) := Apse.gloss H Y
  obtain ⟨τ,hτ⟩ := postingTrial H Y
  have hF (x : ℝ) (_ : x ∈ (Set.univ : Set ℝ)) : UVNext.CouplingReset.target (a:=A.B.a) F x = _ := hτ
  have hx : (0:ℝ) ∈ Set.univ := Set.mem_univ _
  obtain ⟨he,h⟩ := Return.settled (τ:=fun _ => τ) (Q:=F) (a:=fun _=> H.source Y)
    g H.paid hb hX hF hx
  constructor
  ·
    rw [← h] at he
    exact he
  exact (Return.records (a:=fun _=> H.source Y) g H.paid hb hX hx 0).2

end YM.PhysicalNext.Repeat.ClearanceR
