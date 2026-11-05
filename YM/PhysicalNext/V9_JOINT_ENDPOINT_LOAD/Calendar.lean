import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Rain
import YM.Progress.JOINT_CALENDAR.Period
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Picks
import YM.Push.ABSOLUTE_SUMS.Path
import YM.Push.GRID_APPROXIMATION.Roll
import YM.Push.STRESS_FLUX.FreeBridge
import YM.SectorNext.VACUUM_NORMALIZATION.Clinic

/-!
# Joint annulus/Cosmos and endpoint currency at a reusable lawful schedule

Do not choose incompatible chart aperture later. Vote on the length floor before
Rolls, width floor at Rolls, THEN Cafe incl annulus costs, THEN (for example,
with a Protection) wish list of Chi, seed charges and trigger threshold
conventions, and last fees before delay/Bar. Applies also at every within-stage
transition, paying through the full OUTPUT order. Callable with larger floors,
later delays. Other threshold/price producers and the actual history/physical
factor suppliers for RAdvances are separate, not outputs of this work.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Clockwork
open Function Filter Set Lattice Wilson RG Precision Pressure Tree Next.SectorChange
  Next.SectorChange.Rows AnalyticBridge.LocalGaussian Push.SectorMeasure Presented
open AnalyticBridge.AnnulusRatioInsertions AnalyticBridge.AnnulusRatioInsertions.Prism Portfolio
open RG.Supply Testing Push.PriceCompiler Input RG.Shoot Next.Scheduling
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius

structure Cafe where
  r : ℝ
  E : ℝ
  η : ℝ
  L : ℝ
  κ : ℝ

structure Menu where
  q : Chi  -- one and same broadCut & profile in our final application
  θ : ℝ   -- can choose after aperture constants; *not* derived to give plateau implications here
  E : ℝ   -- ancillary polynomial reserve per trigger
  power : ℕ -- degree of trigger cost
  μ : ℝ    -- extra coin for Portfolio
  extent : ℕ
  selection : ℕ
  n : ℕ
  positive : 0<θ
  price_nn : 0≤E

structure Booth where
  Q : Kiosk
  W : Boats
  paint : Paint

variable {G : Gauge} {Z : ChartRatio G} {Q : Teller G} {s : Sheet G} {K : MapPrices}

def Outlet (b : Cafe) (Q : Teller G) (N : Side) (w : ℝ) (Z : ChartRatio G) :=
    ∀ l D n e', ∀ᶠ x : ℝ in atTop, Rates Q N l D n w b.r b.E b.η b.L b.κ e' x Z









abbrev Ann (b : Cafe) (t : Menu) (Q : Teller G) (N : Side) (w x : ℝ) (Z : ChartRatio G) := Rates Q N t.extent t.selection t.n w b.r b.E b.η b.L b.κ t.μ x Z

structure Enough (C : Booth) (b : Cafe) (t : Menu) (Q : Teller G) (Z : ChartRatio G) (w : ℝ) (P : Patch) (x : ℝ) : Prop where
  area : macroR P ≤ radiusB x
  rates : Ann b t Q P.L w x Z
  r4 : Medium C.paint G P Q x
  all {c f : Side} (S : StepData c f) : S.patch=P → ∀ d : Desk G S, Calling Q Z t.q Q.below.power b.r x d →
    Day C.Q t.θ t.E Q.below.order t.power d ∧ Trip d C.W

lemma offer (t : Menu) {b : Cafe} {w : ℝ} (P : Patch) (hP : P.Branches Q.bind G) (hZ : LocalRatio Z) (h : Outlet b Q P.L w Z) :
    ∃ C : Booth, ∀ᶠ x : ℝ in atTop, Enough C b t Q Z w P x := by
  have H := h t.extent t.selection t.n t.μ
  obtain ⟨y,hy⟩ := H.exists
  obtain ⟨B,hB⟩ := stage G P Q Z t.q Q.below.order Q.below.power b.r hy.thermal.slots hZ hP
  obtain ⟨W,hW⟩ := boats G P Q hP b.r hy.thermal.slots
  obtain ⟨color,hC⟩ := painting G P Q hP
  refine ⟨⟨B,W,color⟩,?_⟩
  filter_upwards [hB t.θ t.E t.power t.positive t.price_nn,hW,hC,H,Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR P)] with x hx hW hC h h'
  exact ⟨h',h,hC,fun S hS d hc => ⟨hx S hS d hc,hW S hS d hc (hx S hS d hc)⟩⟩

structure Open (s : Sheet G) (K : MapPrices) (Z : ChartRatio G) (j i : ℕ) (N : Side) (w : ℝ)
    (b : Cafe) (C : Booth) (t : Menu) (x : ℝ) : Prop where
  bills (P : Patch) : P.J=j → P.L=N → Enough C b t (Testing.query s K j i) Z w P x

private instance : Nonempty Booth := ⟨⟨⟨⟨1,1,1,one_pos,one_pos,le_rfl⟩,1,1,1,1⟩,⟨⟨1,1,1,one_pos,one_pos,zero_le_one⟩,1,1,one_pos,one_pos⟩,⟨0,0,0,0,0,0⟩⟩⟩

variable {D : Rolls s} {Θ : Protection D}
  {w : ℕ → ℕ → ℝ} {b : ℕ → ℕ → Cafe} {C : ℕ → ℕ → Booth} {m : ℕ → ℕ → Menu}

def patch (D : Rolls s) {j i : ℕ} (hj : Adj j i) (hs : s.first ≤ i) : Patch := ⟨D.L j,j,s.cut.trans (hs.trans hj.1),(D.large j).size,(D.large j).odd⟩

theorem opened (h : ∀ j i, Adj j i → s.first ≤ i → Outlet (b j i) (Testing.query s K j i) (D.L j) (w j i) Z) (hZ : LocalRatio Z)
    (m : ℕ → ℕ → Menu) : ∃ C : ℕ → ℕ → Booth, ∀ j,∀ᶠ x : ℝ in atTop, ∀ i, Adj j i → s.first ≤ i → Open s K Z j i (D.L j) (w j i) (b j i) (C j i) (m j i) x := by
  have hx (j i : ℕ) : ∃ c : Booth, ∀ᶠ x : ℝ in atTop, Adj j i → s.first ≤ i → Open s K Z j i (D.L j) (w j i) (b j i) c (m j i) x := by
    by_cases hi : Adj j i ∧ s.first ≤ i
    · let P := patch D hi.1 hi.2
      obtain ⟨c,hc⟩ := offer (Q:=Testing.query s K j i) (m j i) P (s.has P) hZ (h j i hi.1 hi.2)
      refine ⟨c,hc.mono fun x hx _ _ => ⟨fun Y h1 h2 => ?_⟩⟩
      have he : Y=P := by cases Y; unfold P patch; congr
      rw [he]; exact hx
    exact ⟨Classical.arbitrary Booth,Eventually.of_forall fun _ a b=>False.elim (hi ⟨a,b⟩)⟩
  choose C hc using hx
  refine ⟨C,fun j => ?_⟩
  filter_upwards [hc j j,hc j (j-1)] with x hA hB i hi hy
  rcases stepStages_target hi with h|h <;> subst i <;> first | exact hA hi hy | exact hB hi hy

def Funded (Z : ChartRatio G) (K : MapPrices) (b : ℕ → ℕ → Cafe) (C : ℕ → ℕ → Booth) (m : ℕ → ℕ → Menu) (w : ℕ → ℕ → ℝ) (W : Delays Θ) := ∀ j x, W.betaEntry j ≤ x → ∀ i, Adj j i → s.first ≤ i → Open s K Z j i (D.L j) (w j i) (b j i) (C j i) (m j i) x

lemma Funded.priors {W : Delays Θ} (h : Funded Z K b C m w W) : Ringing K w W ∧ Cosmos Z K W w (fun j i => (b j i).r) (fun j i => (b j i).E+1) := by
  have he (j i) (hi : Adj j i) (hs : s.first ≤ i) (x) (hx : W.betaEntry j≤x) :=
    ((h j x hx i hi hs).bills (patch D hi hs) rfl rfl).rates.thermal
  refine ⟨⟨fun i j h1 h2 hs => ⟨(he j i ⟨h1,h2⟩ hs _ le_rfl).large, (b j i).κ, (he j i ⟨h1,h2⟩ hs _ le_rfl).rebate, ?_⟩⟩,
    fun j i hi hs => ⟨(he j i hi hs _ le_rfl).slots, by linarith only [(he j i hi hs _ le_rfl).cap], ?_⟩⟩
  · intro x hx c f S hS hr T hT F A U k V hF ha
    have ht := (he j i ⟨h1,h2⟩ hs x hx).location c f S T hS hr hT F A U k V hF ha
    rwa [hS] at ht
  intro x hx N d
  have hf := he j i hi hs x hx; obtain ⟨-,hd,hD,h₁,h₂⟩ := hf.stamp
  refine ⟨hf.frames.2.1,hd,hD,fun t ht => (h₁ t ht).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)),?_⟩
  intro c f S hJ hL hr T hT
  have hb := ((h j x hx i hi hs).bills S.patch hJ hL).area
  have hcf : c.val ≤ f.val := by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
  exact ⟨by omega, by omega,fun A F p k V q => h₂ c f S T hL hr hT A F k V p q⟩

/-- Buy at first exit and self-loops too. Designed for use on EARLY costs
already bumped via `early`/`widths`. Not licensed to replace a fixed w or
star aperture incompatible with those *prior* purchases. -/
theorem book (hZ : LocalRatio Z) (h : ∀ j i, Adj j i → s.first ≤ i → Outlet (b j i) (Testing.query s K j i) (D.L j) (w j i) Z)
    (m : ℕ → ℕ → Menu) (U : Delays Θ) : ∃ (C : ℕ → ℕ → Booth) (W : Delays Θ), OrderedDelays W ∧ DelayLe U W ∧
    ∀ X : Delays Θ, DelayLe W X → Funded Z K b C m w X ∧ Ringing K w X ∧ Cosmos Z K X w (fun j i => (b j i).r) (fun j i => (b j i).E+1) := by
  obtain ⟨C,hC⟩ := opened h hZ m
  obtain ⟨W,hW,hl,H⟩ := delay_extra U _ (fun _ _ _=> True) hC (by simp)
  exact ⟨C,W,hl,hW,fun X hX => let hf : Funded Z K b C m w X := (H X hX).1; ⟨hf,hf.priors⟩⟩
end YM.PhysicalNext.JointLoad.Clockwork
