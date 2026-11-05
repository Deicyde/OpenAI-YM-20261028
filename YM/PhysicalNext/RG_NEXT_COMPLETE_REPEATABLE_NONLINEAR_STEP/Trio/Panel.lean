import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Trio.Star
/-! # Exact loss (physical only if from generation of Enthusiasm)
 From individual short FG & F truncated. Expose all masks, Does B and Γ same. 
 -/
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
variable {G : Gauge} {c f C' F:Side} {j i m n W w r k l h:ℕ} (B : BudgetPoint) {Y:Stars→Side}
section income
variable {S:StepData c f} {K₀:Teller G} {d p a U T' : ℝ} {X: ConnectedActivityE6.Target G K₀} {o: Target.Order G p} {L:Side} {T:Tube G S} {R R': RG.Rep G f}
   {Z : Cash p d a L X o T' T R} {Z':Cash p d a L X o T' T R'}
    (Wt : Match.Alliance Z' Z 1 0) (γ:ℝ) (n:ℕ)
local notation "P" => (B)
local notation "P₀" => (Beam.marquee Z' B)
local notation "O" => Chi.canonical
local notation "h₀" => (plusone Z' Wt O γ)
local notation "h₁" => (Meadow.timbres Wt (χ:=O) γ n)
local notation "R₀" => (Meadow.panel Z' n)
local notation "D₀" => Meadow.studio X.halo (radiusB d)
local notation "f₀" => (Meadow.barony Z O n γ)
variable (Q:∀ i:Stars,(Y i).val=2*(w+i.val)) (z:ℕ) (fa:∀ i:Stars,Offer G (Y i)) (V:Config G c)
abbrev rip (i: Stars) (x:Site (Y i)):Config G (Y i)→ℝ:= Boulevard.stillA (fa i x)
-- Orientation sym by Choir AFTER receipt totals.
def earned (i:Site c) (V:Config G c):= ∑ x∈Meadow.panel Z' n, Meadow.garnerAt Z' B i x *((P₀).read h₀|>.regularOccurrence B x V)
def ornament (o: Site c):= Trio.beacon Q (rip fa) o

def insight (i: Site c) (V:Config G c): ℝ:= Trio.earned B Wt γ n i V - f₀ i 1 - unearned B Q z (rip fa) i V
-- Mask support for logs.
lemma levy (t k : ℝ) (h : Collection.Local (posting B Z') B h₀ t k):
    ((posting B Z').read h₀).additive B V=(P₀|>.read h₁|>.additive B V) + (Fintype.card (Site c):ℝ)* f₀ 0 1 + (∑ i:Site c, masked B.threshold (neighbors z i) (ornament Q fa i) V) + ∑ i, insight B Wt γ n Q z fa i V:= by
  let f:= f₀ 0 1; have hp i: f₀ i 1=f:= by
    rw [show i= Lattice.affine 1 i (0:Site c) from (by simp [Lattice.affine]), Meadow.rotates]; rw [pull_one]; change f₀ 0 (Lattice.translate i 1)=_; rfl
  rw [Meadow.unearned Wt n h]; let v i:= Trio.earned B Wt γ n i V
  have he: ∑ i∈R₀,masked B.threshold ((Beam.marquee Z' B).reg i).support ((h₀).logRead i) V=∑ x:Site c,v x:= by
    unfold v Trio.earned; rw [sum_comm]; symm; refine sum_congr rfl ?_; intro i hi; rw [← sum_mul,Meadow.paysOne,one_mul]; rfl
  rw [he]; unfold ornament; rw [Trio.parade]; simp_rw [Trio.insight,hp]; rw [sum_sub_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul, card_univ]; unfold v f; ring
variable {V}
lemma scrap (s:Site c) (hz:2*z≤k) (hw:w+4≤z) (hp:2*D₀≤ w) (hc:4*D₀+16≤c.val) (hT:B.B=radiusB d) (ha:Z'.supportP=Z.supportP) (hK:R'.path=R.path) (hY:Wt.units=Equiv.refl _) (h : CompatibleP B D₀ f₀ fa) (hV: Healthy B.threshold (neighbors k s) V): insight B Wt γ n Q z fa s V=0:= by
  have he := tinted (f₀) fa h
  have hk : Trio.earned B Wt γ n s V=f₀ s V:= by
    unfold earned; rw [Meadow.aster O B Wt hK ha hY γ n s, Finset.sum_apply]; refine sum_congr rfl ?_; intro i hi
    let A:= (Beam.marquee Z' B).reg i; let F:= (h₀).logRead i
    by_cases H:Meadow.garnerAt Z' B s i=0; · rw [H]; simp
    have hv:= Meadow.assigned Z' B s i hi hT H; have hΩ : Healthy B.threshold A.support V:= hV.mono_left (fun p he=> (neighbors_mem ..).2 (((neighbors_mem ..).1 (hv.2 he)).trans (by omega)))
    exact congr_arg (Meadow.garnerAt Z' B s i * ·) (masked_eq _ _ F V hΩ)
  have hh := Trio.cruising B Q z (rip fa) V s hw hp hz hc hV _ he (by dsimp only [Meadow.studio, Meadow.roomSize]; omega)
  unfold insight; rw [hk, hh]; exact sub_self _
end income
end YM.PhysicalNext.Repeat.Trio
