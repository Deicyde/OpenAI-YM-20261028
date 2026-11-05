import YM.FullVolume.C.Brawn
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Rain.Glazing
/-! Sharpen Prairie bounds with scaled receipts at all applied Real. -/
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
local notation "D₁" => tuneT H he W d
local notation "f₀" => uptick H d
local notation "b₀" => beams H he W d
local notation "i₀" => nights H he W d
local notation "p₀" => opening H
local notation "h₀" => ((c₁+2*c₂)*forecastE A.B.a m + turnFee B*g + g)
section locals
include h hm he hh hx H hc
lemma floe : ∀ i:Site A₀, Shingle.Mild (B) (neighbors e i) (fun x=> b₀ x i) s:= by
  have hK := coating h.conducts hm (fun x hx=> (he x hx).2); have hk := h.agenda _ _ (step_paid A.B.a m)|>.1
  have hv (i:Stars) :∀ j:Site (Rain.moor C A m i), Shingle.Mild B univ (fun x => Yd x i j) s:= W.attunes hm h.conducts.full hh h.jewels hK.decent ⟨hk,hx⟩ i (minute H he) s (hc.beta.congr (fun i hi=> by change (Q (H.latch i)).beta=(Q i).beta; rw [Embrasure.click _ i hi]))
  exact fun i=> Shingle.rising Pu hv (show tent k (radiusB x₀)+4 ≤ e from (by unfold Trio.base; omega)) i
variable (U : Site (A.B.a.S.side m n)) (x : ℝ) (hX:x∈s)
include hX
lemma primed (hU: Meadow.Budget B H.doors.reg ((f₀ x).logRead) h₀) (hB: ∀ i:Site A₀,(B).supBounds i (neighbors e i) (beams H he W d x i) (gleam (A:=A) (C:=C) (m:=m))) :
    Collection.Local (opening H) B (charmT H he W d x) ((h₀) + turnFee (B)*(gleam (C:=C) (m:=m) (A:=A)*Real.exp (preExponent B*coverTicket k))) (forecastK A.B.a m S (Q x).beta):= by
  let D' := lens H; let W':= i₀ x; let V := b₀ x; let Y := f₀ x; let c':= (gleam (A:=A) (C:=C) (m:=m)); let s':= c'*Real.exp (preExponent B*coverTicket k)
  have he' i:= (floe h hm H hc he hh hx W d) i|>.smooth x hX
  have hv:0≤ c':=(hB 0).1
  have hF : Meadow.Budget B (leap e) V s':= by
    refine ⟨fun _=>c',fun i=>?_,fun i=>⟨he' i,hB i⟩⟩; apply budget_finite
    · intro i; split; exact mul_nonneg hv (Real.exp_pos _).le; rfl
    rw [Finset.sum_eq_single i]; rw [if_pos (show (leap e i).site=i from rfl)]
    · apply mul_le_mul_of_nonneg_left _ hv; apply Real.exp_monotone; apply mul_le_mul_of_nonneg_left _ (headline B|>.exponent_pos.le); unfold coverTicket; apply Nat.cast_le.mpr; apply (Trio.scaleMeters k (radiusB x₀) (B).B_pos i e (by omega)).trans; rw [two_mul]
    · intro j hj he; exact if_neg he
    simp
  have hm : ∀ s b,Nonempty ((H.doors.read Y).Moves s b):= fun s b=> Beam.moves _ _ O _ s b _
  have hp:= Marlin.reg_bison H.doors e (2*e) Y V W' hU hF
  have hs:= Marlin.sous (lavish h ‹m<N› H hc he hh hx W d x hX) hp (fun s b=> Marlin.reeds _ _ _ Y V W' s b (hm s b|>.some))
  exact hs
end locals
end YM.PhysicalNext.Repeat.Rain
