import YM.FullVolume.C.Zero
import YM.FullVolume.C.Echo
/-! Full layout controls, including Off trajectories. Obtain uniform retirement at fixed N,m,p and given INCOMING layout. Does not require even unit analysis on those columns. Deck chosen once before launching. No decisions using input coefficients incl equality. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Rain
open Function Filter Set Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard Marlin Lantern Trio Roof
open Progress.DirectedRecipe Time
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
-- compact socket avoids Pie SAM goals; not obligation records encoding analytic estimates.
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
variable {G : Gauge} {X:Metals G} {D:Rolls X.p} {A : Alloy X D} {C:Targets X.p X.K} {Z:Expenses C} {F : ℕ→ℕ→Postage} {S:Time.Scouts (F:=F)} {p : Return.Wages} {s: Set ℝ} {v:ℕ→ℝ} {R:Register D Z p v} {E:ℕ→ℕ→Exchange} {bt:Baton G} {u t : Return.Wages} {Bn:ℕ→ℕ→Booth} {J:ℕ→ℕ→JointLoad.Clockwork.Menu} {P:ℕ→ℕ→JointLoad.Heir.Record} {L : ℕ→ℕ→JointLoad.Folio.Aux} {c c₁ c₂:ℝ} {q:UVNext.CouplingReset.ResetPrices} {η:ℕ→ℝ} {r:ℕ→ℕ→ℕ} {T:Programs X.p} {Y: ℕ→ℕ→Cafe}
    (h : Roof.Sheltered (C:=T) (B:=Y) A bt u t r Bn J P L R S c₁ c₂ (1/8) E q η)
    {N m n : ℕ} {Q: UVNext.CouplingReset.In A.B.a m n} {a:ℝ} (hm: m<N)
local notation "x₀" => A.B.a.clock.hatBeta m
local notation "A₀" => A.B.a.S.side m n
local notation "B" => (A.B.a.budget m)
local notation "k" => Rain.lint C A m
local notation "e" => Trio.base k (radiusB x₀)
local notation "Jp" => A.B.a.clock.J (m+1)
local notation "Ip" => A.B.a.clock.J m
local notation "L₀" => D.L Jp
local notation "g" => gold G L₀ x₀
local notation "γ" => A.B.kin.alpha N m
-- Note hL syntax names
variable (H : Roof.Embrasure (U:=A) (Y:=R) (N:=N) (n:=n) Q s a)
variable (hc : Curve (A.B.a.budget (m+1)) Q s) (he : ∀ x∈s,Lives (Roof.spatial A).bake N (m+1) n (Q x) ∧ (Q x).beta ∈ band A.B.a (m+1)) (hh : WorksIn R A.post A.delay S)
   (hx:(C (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).table=X.O) (ht:AsDivisors A.B.a.S) (hl: (Z (A.B.a.clock.J (m+1)) (A.B.a.clock.J m)).wanting= -(7/16:ℝ))
    (W:Zeal C R A N m) (d:ℕ)
local notation "D₀" => Meadow.studio (Rain.lint C A m) (radiusB x₀)
set_option quotPrecheck false
local notation "Z₀" => (Z Jp Ip).wanting
local notation "Pu" => (screens C A m)
local notation "Yd" => fun (x:ℝ)=> W.offers d (Rain.minute H he x)
local notation "O" => Chi.canonical
variable {x:ℝ}

-- phase-independent eligibility through arbitrary Storm applicants. Curve version kernel unchanged.
section general
include h hc he hm
lemma verdict (ha:a∈s): ∃ H:Roof.Embrasure (N:=N) (Y:=R) (U:=A) Q s a, True:=by
  choose f H using fun (t:s) => Roof.prepares h.conducts hm (he t t.2).1 (he t t.2).2
  exact ⟨⟨f,H,ha,fun i=> Match.staple (((he a ha).1.path).trans (he i i.2).1.path.symm) (hc.reg _ ha _ i.2) (hc.forced _ ha _ i.2),fun _=>rfl⟩,trivial⟩
include H
lemma budge {i} (hx : x∈s) : (if Meadow.debris H.base d i then (H.fullSong x).logRead i else 0) = if Meadow.debris (H.houses (H.latch x)) d i then (plusone (H.houses (H.latch x)) (Match.staple (J:=H.houses (H.latch x)) rfl rfl rfl) O γ).logRead i else 0 := by
  let y:= H.latch x
  have hq := ((he _ H.he).1.path.trans (he _ y.2).1.path.symm)
  have hK := hc.reg _ H.he _ y.2; have hv:= hc.forced _ H.he _ y.2
  have hz: Meadow.debris H.base d i ↔ Meadow.debris (H.houses y) d i:= Meadow.stamped hq hK hv d i
  unfold Embrasure.fullSong
  rw [Meadow.upward O (H.sister (H.latch x)) (H.agrees (H.latch x)) hq hK hv γ (I':=H.houses y)]
  exact if_congr hz rfl rfl
end general
section assign
local notation "T'" => A.B.a.S.side (m+1) n

def listIn {n:Side} (Y: Rep G n) : Listing G n:= ⟨Y.activities.reg,Y.activities.forced⟩

structure Retired (R:Register D Z p v) (A : Alloy X D) (W:Zeal C R A N m) (n:ℕ) (c₁ c₂: ℝ) (L:Listing G (A.B.a.S.side (m+1) n)) (d:ℕ) : Prop where
  emits : ∀ {s: Set ℝ} {a:ℝ} (Q: UVNext.CouplingReset.In A.B.a m n) (H:Roof.Embrasure (N:=N) (Y:=R) (U:=A) Q s a) (_hc:Curve (A.B.a.budget (m+1)) Q s) (he : ∀ x∈s,Lives (Roof.spatial A).bake N (m+1) n (Q x) ∧ (Q x).beta∈band A.B.a (m+1)), listIn (Q a)=L → ∀ x∈s,
      Meadow.Budget (A.B.a.budget m) H.doors.reg (uptick H d x|>.logRead) ((c₁+2*c₂)*forecastE A.B.a m+turnFee (A.B.a.budget m)*gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)+gold G (D.L (A.B.a.clock.J (m+1))) (A.B.a.clock.hatBeta m)) ∧ ∀ j:Site (A.B.a.S.side m n),(A.B.a.budget m).supBounds j (neighbors (Trio.base (Rain.lint C A m) (radiusB (A.B.a.clock.hatBeta m))) j) (beams H he W d x j) (gleam (A:=A) (C:=C) (m:=m))

include h hm hh
include hc he
private lemma printed (x:ℝ) (hX:x∈s) (hd: Meadow.Budget B H.doors.reg (fun i=> if Meadow.debris H.base d i then (H.fullSong x).logRead i else 0) g) : Meadow.Budget B H.doors.reg (uptick H d x|>.logRead) (((c₁+2*c₂)*forecastE A.B.a m + turnFee B*g) + g):= by
  let y:=H.latch x; let T:= ships A.B N m n; have hy:T.down.Bounds T.low (A.B.a.params m).width (A.B.a.params m).paths (A.B.a.clock.loopCap m):= A.B.support.cap _ _ hm.le
  have hk:= H.houses y; have hQ:= suns R A hh.chip hm (A.B.a.S.oneStep m n).exact_size (H.houses y); have ha:= he _ H.he; have hY:= he y.val y.2
  have hP:(Q a).path= (Q y).path:= ha.1.path.trans hY.1.path.symm
  have hr₁ := hc.reg _ H.he _ y.2
  have hr₂ := hc.forced _ H.he _ y.2
  have hr := Roof.seats h.conducts h.peak h.jewels h.pipes h.agenda hm hY.1 hY.2 H.base (H.houses y) (H.honors y) (H.sister y) (H.agrees _) hP hr₁ hr₂
  exact Meadow.candles (χ:= O) (H.sister (H.latch x)) (B) γ d (Meadow.podiumAll (H.sister (H.latch x)) (B) γ hP.symm hr₁ hr₂ (H.agrees _) hr rfl hy ((coating h.conducts hm (fun x hx=> (he x hx).2)).decent) hQ.1 hQ.2.2) hd
omit hc he
include W hx ht
set_option maxHeartbeats 600000 in
lemma celebrates (f:Listing G (T')) : ∀ᶠ d in atTop, Retired R A W n c₁ c₂ f d:=by
  by_cases hA: ∃ u, Lives (Roof.spatial A).bake N (m+1) n u ∧ u.beta∈band A.B.a (m+1) ∧ listIn u=f
  swap
  · filter_upwards with d; exact ⟨fun Q H h he hr=> False.elim (hA ⟨_,(he _ H.he).1,(he _ H.he).2,hr⟩)⟩
  obtain ⟨U,hU,hB,rfl⟩:=hA
  let T:= initialBed U; let V:= band A.B.a (m+1)
  have hT: ∀ x∈ V,Lives (Roof.spatial A).bake N (m+1) n (T x) ∧ (T x).beta∈V:= fun x hx=> ⟨⟨hU.path,hU.point,hU.clip,⟨hU.valid.paths,initialBed_valid U hU.valid.labels x⟩,trivial⟩,hx⟩
  have hc₁: Curve (A.B.a.budget (m+1)) T V:= (show U.p=A.B.a.budget (m+1) from hU.point) ▸ initialBed_curve U V
  let P:= (verdict h hm hc₁ hT hB).choose; let I₀:= Beam.marquee P.base (B)
  have hG : 0<(g):= by rw [gold, ← PriceCompiler.beta_eq A.B.valid]; exact Real.rpow_pos_of_pos (zero_lt_one.trans (A.B.a.fits.delayed _)) _
  have h' := Meadow.cashier (Z:=posting B P.base) (H:=I₀) (s:=V) (fun i=>(Beam.rewrite_rule P.base (B) i).symm) (B) (Meadow.debris P.base) isCompact_Icc (Meadow.dissolved P.base) (Yearling.screen h.conducts P hT hc₁ hh.year h.range hm) (fun x hy=> ⟨_,_,masts h hm P hT hh x⟩) g hG
  filter_upwards [h',shone h hm P hT hh hx ht W] with d ha hy
  refine ⟨?_⟩; intro s a Q H hc he hr x hX
  let y:= H.latch x; obtain ⟨hp,hK⟩:= he y.val y.2
  let z:= (Q y).beta; have ht: z∈V:=hK; let D':= P.houses (P.latch z); let U':= T (P.latch z)
  have hY:= hT _ (P.latch z).2; have hv:minute P hT z=minute H he x:= Subtype.ext (by change (T (P.latch z)).beta=z; rw [Embrasure.click _ z ht]; rfl)
  refine ⟨?_,fun i=>by
    have hh := hy z ht i; unfold beams at *; rw [hv] at hh; exact hh⟩
  let Z:= H.houses y
  have ha' := (he _ H.he).1
  have hP := hc.reg _ H.he _ y.2; have hQ:=hc.forced _ H.he _ y.2; have hU₀:= ha'.path.trans hp.path.symm
  have hE: U'.activities.reg=(Q y).activities.reg:= (congr_arg Collection.Listing.reg hr).symm.trans hP
  have hI: U'.activities.forced=(Q y).activities.forced:= (congr_arg Collection.Listing.hard hr).symm.trans hQ
  have hZ:= hY.1.path.trans hp.path.symm
  apply printed h hm H hc he hh d x hX
  have h' := ha z ht
  let i:= P.latch z; have hu₀: (T U.beta).path = (Q a).path := (hT _ P.he).1.path.trans ha'.path.symm
  have hu₁: (T U.beta).activities.reg = (Q a).activities.reg:= (congr_arg Collection.Listing.reg hr).symm
  have hu₂: (T U.beta).activities.forced = (Q a).activities.forced:= (congr_arg Collection.Listing.hard hr).symm
  have hd : I₀=H.doors := Meadow.signage hu₀ hu₁ hu₂ _
  let M:= Match.staple (H:=D') (J:=Z) hZ hE hI
  have hf : U'.beta=(Q y).beta:= congr_arg Subtype.val hv
  have hr j : (if Meadow.debris P.base d j then (P.fullSong z).logRead j else 0)= (if Meadow.debris H.base d j then (H.fullSong x).logRead j else 0):= by
    rw [budge h hm H hc he d hX,budge h hm P hc₁ hT d ht]
    split
    next hb => have hs: Meadow.debris D' d j:= hb; rw [if_pos ((Meadow.stamped (I:=Z) hZ hE hI d j).1 hs)]
               exact (Meadow.wires O M rfl hZ hE hI (hY.1.clip.trans hp.clip.symm) hf (hY.1.point.trans hp.point.symm) d j hs γ).trans (congr_arg (fun (v:Collection.Source G A₀)=>v.logRead j) (Meadow.upward O M rfl hZ hE hI γ (I':=Z)))
    next hb => symm; exact if_neg (show ¬Meadow.debris Z d j from fun h'=> hb ((Meadow.stamped (H:=D') hZ hE hI d j).2 h'))
  rwa [hd, show (fun j=>_)=(fun j=>_) from funext hr] at h'
end assign
end YM.PhysicalNext.Repeat.Rain
