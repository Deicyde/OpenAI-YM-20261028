import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Slide.Mover
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Panel
/-! # Loose eligibility, reg incidence at BASE/horns. No perturbative amplitudes anomaly
    even at equality of markers. price of finite LF requires exact μ posts. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Trio
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo RG.Shoot
open Push.Uniform Brush Blaze.Frond Sienna Fare Lapis Metric Further.LogJets Height Roof Input Org Supply Pane Slide
open Push.PriceCompiler ThroughLaunch Height Opera Boulevard
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C' F:Side} {j i m n W w r k l:ℕ} (B : BudgetPoint) {Y:Stars→Side}
section inner
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i)) (h : ∀ i j, B.Regular univ (fa i j)) (hp:w+4≤ z)
include h hp
lemma unit_m (x: Site c) (i:Stars) (j:Site (Y i)): B.Regular (neighbors z x) (unit Q (rip fa) i j x):= by
  apply Slide.regular (pad Q i) x (show B.Regular univ (rip fa i j) from CouplingShape.reg_sub (h i j) (CouplingShape.reg_const _))
  intro j; have hu:=Slide.village (C:=Y i) (w:=w+i.val) (Q i).ge x j; exact (neighbors_mem ..).2 (hu.trans (by have hx:= i.isLt; omega))


-- Local geometry filler
end inner
variable {U : Type*}
structure Tidy (X: Support c) (t: Config G c→ℝ) : Prop where
  uses : UsesFinal B.threshold X t
  borel : Measurable t
  invariant : GaugeInvariant t
lemma tidy_sub {X:Support c} {u v:Config G c→ℝ} (h:Tidy B X u) (ht:Tidy B X v): Tidy B X (u-v) := ⟨fun x y hi he=>congr_arg₂ (·-·) (h.uses x y hi he) (ht.uses x y hi he), h.borel.sub ht.borel, fun x y=> congr_arg₂ (·-·) (h.invariant x y) (ht.invariant x y)⟩
lemma tidy_const {X:Support c} (t:ℝ) : Tidy (G:=G) B X (fun _=>t):= ⟨fun _ _ _ _=>rfl, measurable_const,fun _ _=>rfl⟩
lemma tidy_sum {ι:Type} (X: Support c) (s:Finset ι) (R:ι→ Config G c→ℝ) (h:∀ i∈s,Tidy B X (R i)): Tidy B X (fun U=>∑ i∈s,R i U):= ⟨fun U V hu he=> sum_congr rfl (fun i hi=> (h i hi).uses U V hu he), Finset.measurable_fun_sum _ fun i hi=> (h i hi).borel, fun x V=> sum_congr rfl (fun i hi=>(h i hi).invariant x V)⟩ -- lemma name
lemma tidy_scale {X : Support c} {u: Config G c→ℝ} (a:ℝ) (h : Tidy B X u): Tidy B X (fun V=> a* u V):= ⟨fun _ _ he hu=> congr_arg _ (h.uses _ _ he hu), h.borel.const_mul _, fun x y=> congr_arg _ (h.invariant x y)⟩
lemma tidy_mask {X Z: Support c} {t:Config G c→ℝ} (h:B.Regular X t) (he:X⊆Z): Tidy B Z (masked B.threshold X t):= ⟨fun x y ht hv=> CouplingShape.stencil_reads _ h.sites _ x y (agrees_mono ht he) (by
  change X∩_ = X∩_; have hz: X∩Z=X:= inter_eq_left.mpr he; rw [← hz,inter_assoc,hv, ← inter_assoc]),masked_measurable _ _ _ h.borel, CouplingShape.stencil_gi h.symmetry _ _⟩

section lo
variable {S:StepData c f} {K₀:Teller G} {d p a U T' : ℝ} {X: ConnectedActivityE6.Target G K₀} {o: Target.Order G p} {L:Side} {T:Tube G S} {R R': RG.Rep G f}
   {Z : Cash p d a L X o T' T R} {Z':Cash p d a L X o T' T R'}
    (Wt : Match.Alliance Z' Z 1 0) (γ:ℝ) (n:ℕ) (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa: ∀ i:Stars,Offer G (Y i))
    (u:Site c) (hq : ∀ i,B.Regular ((posting B Z').reg i).support ((plusone Z' Wt Chi.canonical γ).logRead i))
    (hP : ∀ i j, B.Regular univ (fa i j))
local notation "P" => (B)
local notation "P₀" => (Beam.marquee Z' B)
local notation "O" => Chi.canonical
local notation "h₀" => (plusone Z' Wt O γ)
local notation "h₁" => (Meadow.timbres Wt (χ:=O) γ n)
local notation "R₀" => (Meadow.panel Z' n)
local notation "D₀" => Meadow.studio X.halo (radiusB d)
local notation "f₀" => (Meadow.barony Z O n γ)
include hq hP
lemma prim (hp:w+4 ≤z) (he:D₀ ≤ k) (hk : 2*z ≤ k) (hV : B.B=Pressure.radiusB d) : Tidy B (neighbors k u) (insight B Wt γ n Q z fa u):= by
  let V i := Trio.unearned B Q z (rip fa) u i
  refine tidy_sub B (v:=V) (u:= Trio.earned B Wt γ n u - fun _ : Config G c=> f₀ u 1) ?_ ?_
  · apply tidy_sub _ _ (tidy_const ..)
    refine tidy_sum _ _ R₀ _ fun i hi=> ?_; by_cases hB: Meadow.garnerAt Z' B u i=0; · simp only [hB,zero_mul]; exact tidy_const ..
    refine tidy_scale _ _ (tidy_mask _ (X:=((P₀).reg i).support) ?_ ?_)
    · rw [Beam.rewrite_rule]; exact hq i
    intro j hj; apply (neighbors_mem ..).2; exact ((neighbors_mem ..).1 ((Meadow.assigned Z' B u i hi hV hB).2 hj)).trans he
  refine tidy_sum _ _ _ _ fun i _=> tidy_scale _ _ (tidy_sum _ _ _ _ fun j _=> tidy_mask _ (unit_m B Q z fa hP hp (emerge Q i j u) i j) (patch Q z hp i j u hk)) -- pattern
end lo
end YM.PhysicalNext.Repeat.Trio
