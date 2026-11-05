import YM.FullVolume.Gain.Rate
/-!
# Lyrics full records for **all** Competes V.t.Trail, common charts. Articulus. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Muse
open Function Filter Set Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Animals
open MeasureTheory ProbabilityTheory Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Height Input Org Supply Pane Slide
open Push.PriceCompiler Progress.DirectedRecipe Jams Apse Empire Time Roof Chord Ovens
open FullVolume.Ray FullVolume.Urns FullVolume.Amp Pass Tent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
variable (g:G.Simple){v q d t t':ℝ}{N n m:ℕ}(L: Lyrics R t t)(h:Degree R.shape R.scout A.delay)(hq:Savvy R.scout R.target A.delay q v d t)
open UniformSpace
section M
variable {T:Team (stageP A.B.a N n)} (ht:Top N n T)
set_option maxHeartbeats 800000
local notation "Ω"=> A.B.a.clock.hatBeta N
variable (hr:Planned.Port.AtTop A.B.kin)(hu:Tent.Credit A.delay t')(hC:choir q)(hY:Climate (A.B.a.clock.hatBeta N))(R)
include R hr hC hu hY ht
local notation "e"=> ContinuousLinearMap.id ℝ ℝ
lemma bootN (hb:q/2 ≤ grand Ω) {x:ℝ} (hv:mild Ω x): ‖World.ready (Yawn ht x)‖≤4*t':=by
  have hg:=hC.1; have hh:= instruct R ht hu hr hY (by linarith:1≤q/2) hb (samples hY hv (show |x-x|≤2 from (by norm_num))) (v:=0) (by norm_num)
  exact (show _ ≤ _ from (by simpa using solo hh Jams.tip) : ‖Yawn ht x‖≤4*t')
lemma bootP (hb:q/2 ≤ grand Ω)(hd: 2*(4*t') ≤ FullVolume.Amp.glint) {x:ℝ}(hv:mild Ω x):∃ P:FullVolume.Amp.Pulse ℝ (World T) FullVolume.Amp.glint, Hits (f:=fun y=>World.ready (Yawn ht y)) (ContinuousLinearMap.id ℝ ℝ) x P:=by
  have hh:= hC.1
  apply exitP e x hC isometry_id denseRange_id hd; refine ⟨by norm_num,?_⟩; filter_upwards [Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<2)] with z hz
  intro y hy; apply roundTrip _ _ hh; have h : |z-x|≤ 2:=by simpa [Metric.mem_closedBall,Real.dist_eq] using hz
  exact (instruct R ht hu hr hY (by linarith : 1≤q/2) hb (samples hY hv h) (show |y|≤1 from hy.trans (by norm_num)))
lemma bootD (hb:q/2 ≤ grand Ω)(hd: 2*(4*t') ≤ FullVolume.Amp.glint){x y:ℝ}(hv:mild Ω x)(hx:mild Ω y): ‖World.ready (Yawn ht y)-World.ready (Yawn ht x)‖ ≤ 8*FullVolume.Amp.glint*‖y-x‖:=by
   obtain ⟨P,hP⟩:= bootP R ht hr hu hC hY hb hd hv -- field order
   by_cases hp:‖y-x‖≤1/4
   · exact (hP.wave hp isometry_id).trans (mul_le_mul_of_nonneg_right (by norm_num [FullVolume.Amp.glint]) (norm_nonneg _))
   apply (norm_sub_le ..).trans; push Not at hp; have hh:= bootN R ht hr hu hC hY hb hv; have h:= bootN R ht hr hu hC hY hb hx; nlinarith [FullVolume.Amp.tintP.1]
end M
local notation "W"=> A.B.a
-- additional Ramp conditions small-Σ from later.
def brace (a:Levels G)(m:ℕ):= salary (a.clock.hatBeta m)
abbrev stow (a:Levels G)(v:ℝ)(m:ℕ):=2*fn a m v
structure Search (a:Levels G)(q v:ℝ):Prop where
   scale (m:ℕ): Climate (a.clock.hatBeta m)
   radiusY (m:ℕ): q/2 ≤ grand (a.clock.hatBeta m)
   pride (m:ℕ) : brace a 0 ≤ brace a m
   radiusB (m:ℕ):∑ i ∈ Finset.range m, stow a v i ≤ FullVolume.Amp.glint*brace a m
structure Plato (L: Lyrics R t t)(q v d a:ℝ):Prop where
   Shears:Degree R.shape R.scout A.delay
   Saved : Savvy R.scout R.target A.delay q v d t
   earn : 2*d ≤ FullVolume.Amp.glint
   voices : choir q
   Clever:Tent.Credit A.delay a
   Lead: Planned.Port.AtTop A.B.kin
   largeG : Search A.B.a q v
   gate : 2*(4*a) ≤ FullVolume.Amp.glint
   begins : L.start= launch (A:=A)
   SimpleR : G.Simple
   firm: Drifting A.B.a
open Plato
variable {L} (Φ : Plato (R:=R) (t:=t) L q v d t')
abbrev Ops (L: Lyrics R t t) (N n:ℕ) := Pass.Circle N n (fun m h=> L.prim N m n h)
variable (O: Ops L N n)
include Φ
lemma opal : Nonempty (Ops L N n):= Pass.cycle Φ.SimpleR (fun m h=>L.prim N m n h) Φ.Clever Φ.Lead
omit Φ
structure Contest (N n:ℕ) (L: Lyrics R t t) where
   trail : Trail A.B.a n
   rises : Competes L.tunes n N 0 trail
   baseB : (trail 0).beta ∈ FullVolume.nearby A.B.a
variable (p: Contest N n L)
namespace Contest
lemma contour (i:ℕ) (h:i≤N): (p.trail i).beta∈band A.B.a i:= (p.rises.prices i (Nat.zero_le _) h).2
lemma twines (i:ℕ) (h:i<N): ∃ x:Chord.Flight A N i n, x.val=p.trail (i+1) ∧ p.trail i=(L.prim N i n h).moment x:= by
   obtain ⟨hp,h⟩:= (p.rises.persists i (Nat.zero_le i) h).continues.2; exact h
include Φ
lemma bound (i:ℕ)(h:i≤N):3/4*A.B.a.clock.hatBeta i ≤ (p.trail i).beta ∧ (p.trail i).beta ≤ 5/4*A.B.a.clock.hatBeta i:= FullVolume.deep_margin L.tunes Φ.firm n N _ p.rises p.baseB i h
def script (i):=toLambda (A.B.a.clock.hatBeta i) (p.trail i).beta -- paren
lemma spoken (i:ℕ)(h:i≤N): fromLambda (A.B.a.clock.hatBeta i) (toLambda (A.B.a.clock.hatBeta i) (p.trail i).beta)= (p.trail i).beta:= (currency (Φ.largeG.scale i).floor ((mul_nonneg (by norm_num) (Φ.largeG.scale i).floor.le).trans (p.bound Φ i h).1)).1
lemma mildS (i) (h:i≤N): mild (A.B.a.clock.hatBeta i) (toLambda (A.B.a.clock.hatBeta i) (p.trail i).beta):= good_mild (Φ.largeG.scale _) (p.bound Φ i h)
lemma startStory: p.trail N=Tent.launch (A:=A) N n (p.trail N).beta:=by rw [← Φ.begins]; exact p.rises.fromTop.inits.2.symm
-- uniqueness of observe. point Reps field equal budgets.
omit Φ in
lemma umpire {x':Activities G (A.B.a.S.side m n)} {T:Team (stageP A.B.a m n)} (x y:Home T)(he: observe T x=x')(h:observe T y=x'): x=y:=by
   have hp:=he.trans h.symm; apply Subtype.ext; apply Show.peek.injective; apply Subtype.ext; exact Prod.ext (congr_arg Activities.E hp) (congr_arg Activities.K hp)
include O
lemma framed (i) (h:i≤N): Nonempty (Row N i n (O.plan i h) (p.trail i)):=by
   induction h using Nat.decreasingInduction with
   | self=> exact (startStory Φ p) ▸ O.receives ⟨_,p.contour N le_rfl⟩
   | of_succ m hm ih =>
     obtain ⟨x,he,h⟩:=p.twines m hm; rw [h]; apply O.walks m hm ⟨x, he ▸ ih⟩
def homeP (i:ℕ)(h:i≤N): Home (O.plan i h):= (Classical.choice (p.framed Φ O i h)).val
lemma home_observe (i:ℕ)(h:i≤N): observe (O.plan i h) (p.homeP Φ O i h)=(p.trail i).activities:= (Classical.choice (p.framed Φ O i h) |>.property : observe _ ((Classical.choice (p.framed Φ O i h)).val)=_)
lemma homeN (i:ℕ)(h:i≤N): ‖p.homeP Φ O i h‖≤1:= by
   let U:= O.plan i h; let x:= p.homeP Φ O i h; change ‖x.val‖≤1; apply (Show.budget ..).mpr; let K:= (p.rises.prices i (Nat.zero_le _) h).1; have hb:=K.valid.labels; rw [K.point,← home_observe Φ O p i h] at hb
   exact more (show FullVolume.Urns.Cash .. from ⟨hb.regular,hb.forced,hb.boundE,hb.boundK⟩) (by rw [one_mul]; rfl) (by rw [one_mul]; rfl)
end Contest
end YM.PhysicalNext.Repeat.Muse
