import YM.RemainderComparison.Cadenza.Bayou
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Cadenza
open Function Filter Lattice RG Pressure Pressure.Testing Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open Height Input Org Supply Pane Push.PriceCompiler ThroughLaunch Bid Planned.JetPort
open YM.RemainderComparison.Aux Funk Herbal
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {P:Teller G} {Q:ConnectedActivityE6.Target G P} {p:Patch} {L : Side} {K:KernelChoices} {j n r : ℕ}
variable {q o w : ℝ→ℝ}{W μ:ℝ} {A:ConnectedActivityE6.Target.Order G W}
open Brim
open PhysicalNext JointLoad Heir
variable (Q:ConnectedActivityE6.Target G P) (A:ConnectedActivityE6.Target.Order G W)
variable {P' B:BudgetPoint} (p:Patch)(r:Rays)(s:Songbook G p.L)
variable {M: RG.Stage}{x η:ℝ}
/-! # Actual step allowances before other transport costs

The K reclosure uses a genuine retained seed existential, not charging
 `s` by truncated EXP path tails. Covers alpha callbacks at all C actual
 supports. Money functions post-L. Probe derivatives conditional on AP
 instruction, not monetary condition varying with fields beyond SCAPE prices. -/
variable (t : Scrollwork G p.L) (E' : RG.Stage)(D : Quarry)
local notation "G'"=>Funk.Platform
local notation "Ψ"=>D.layer p s t E' r
local notation "Y'" => D.gold
local notation "Γ"=>r.rank
open WickReps Trio
open Expenditure
-- READY WEATHER in BODY. Whistle used before realizing virtual charts.
variable (K:KernelChoices)(E:RG.Stage)(C: Libretto G E'.order)(D':Record)(χ:Chi)
structure Coaxes (j:ℕ)(f:ℝ→ℝ) (η δ:ℝ)(x:ℝ):Prop where
    lantern : Poster.Paid r E E' K Q D.toPoster t s x (A:=A) (μ:=μ) -- syntax order
    stamps : Instructions Q A p s (μ:=μ) χ E' r C j t D D' x
    active (β:ℝ)(Z:BudgetPoint)(ht:Temper Z E' x G p.L)(he:inBand (betaF G x p.L) β):
       Funk.Treasury (G:=G) (L:=p.L) K (D.layer p s t E' r x) (D.gold x) Z β x ∧ t.Ready x G Z β (D.R x) ∧ Harmonious p r s t E' D x β Z ∧ Summits p r s t E' D x β f η δ
    resonance (β:ℝ)(Z:BudgetPoint)(ht:Temper Z E' x G p.L)(he:inBand (betaF G x p.L) β): Tuba.Beyond Q p r s t E' D μ x β Z δ
    tolerance (β:ℝ)(Z:BudgetPoint)(ht:Temper Z E' x G p.L)(he:inBand (betaF G x p.L) β): Tuba.Tempo.Heighto p r s t D E' x β f η
structure Allot (j:ℕ)(f:ℝ→ℝ)(η δ:ℝ)(P₀:ℝ): Prop where
    length : D.Financed G p.L Q.rate
    expenses : ∀ x:ℝ, P₀ ≤ x→ Coaxes Q A p r s t E' D (μ:=μ) K E C D' χ j f η δ x

def Quay (L:Side):Prop:=∀ p:Patch,p.L=L →p.Branches P.bind G→∀ (W μ:ℝ) (A:ConnectedActivityE6.Target.Order G W),0<W→0<μ→∀ (s:Songbook G p.L)(t:Scrollwork G p.L)(χ:Chi) (F F':RG.Stage) (r:Rays), r.Heart F' Q.exp→∀ (C:Libretto G F'.order)(R:Record),R.ε≤1/4 →∀ (j:ℕ) (f:ℝ→ℝ) (η δ:ℝ),0<η→0<δ→Reserve G p.L f→ ∃ D P₁, D.d>0∧PaintSupply G r.wind D.Z∧ Allot Q A p r s t F' D (μ:=μ) K F C R χ j f η δ P₁
lemma buoys (hG : G.Simple)(hQ : 3/8+Q.rate<0): ∃ n:ℕ,∀ L:Side, n≤L.val → Quay Q K L :=by
   obtain ⟨n,hn⟩:= Cadenza.rollBefore Q hG hQ
   refine ⟨n,fun L hL p hp hD W μ A hW hμ s t χ F F' r h C R hR j f η δ hη hδ hf=>?_⟩
   obtain ⟨D,hd,hz,hN,hq⟩:= Poster.quorum F F' K Q (A:=A) r t s hμ h
   obtain ⟨B,rfl,hB,hT⟩:= hn p (hp.symm ▸ hL) hD W μ A hW hμ r s t χ j F' h C R hR D hN
   have hW : ∀ᶠ x in atTop, Coaxes Q A p r s t F' B (μ:=μ) K F C R χ j f η δ x:=by
      filter_upwards [hq,hT, Expenditure.swings p r s t F' B hB hz.1 hd _ h Q.stop, expedites p r s t F' B hd hz.1 hB f η δ hf hη hδ, Access.wide hN.afford.rate,Sleet.gustLine s.chord s.skies s.hope.rate (r.p+1),t.growth,Tuba.financed Q p r s t F' B hB hd hz.1 _ h hμ Q.stop δ,Tuba.Tempo.grace p r s t F' B hB hd hz.1 f η hf hη] with x hp hc hβ he ht hm hr hvv hW
      refine ⟨hp,hc,(fun β Z hZ hY=>?_), fun β Z hm he=> hvv Z hm β he,fun β Z hM hL=> hW β hL Z hM⟩
      obtain ⟨hV,hv⟩:=Paid.approved F F' K Q B.toPoster A hp hZ hY hr
      refine ⟨⟨?_,h.absolute,hZ.pose,hZ.pressure,hZ.order.trans_le h.price,hZ.power.le,hZ.salary.trans_le (h.just.trans ((le_add_of_nonneg_right zero_le_one).trans h.light)),hp.soothe.rich,((ht.2 _ hY).2.trans (ht.1.2.1.trans ht.1.2.2.1)).le,hV,s.skies.le,(le_abs_self _).trans (hm.2 _ hY)⟩,hv,hβ _ hZ _ hY,he _ hY⟩
      rw [hZ.order]; exact hp.fund
   obtain ⟨y,hy⟩:= eventually_atTop.mp hW; exact ⟨B,y,hd,hz,hB,hy⟩

-- shade at possession from local grant weather. No need assume sign of wages.
variable {c : Side}{V:Teller G}{Λ:Platform}{Y:Currency}
variable {β γ L':ℝ} {α ι:Type*}
private lemma taxV (g:Config G c→ℝ)(Z:BudgetPoint)(hm:Portal.Mare Z g β γ L')(h:1≤γ) : 0≤ L':=by
   have hp : flags Z.threshold (Arc.route G β (0:Positions (Uniform.Primary c G)))=∅:=by
      rw [show Arc.route G β (0:Positions (Uniform.Primary c G))=1 from (by ext i; rw [Arc.route,smul_zero,actual,represent_link,map_zero]; simp)]; exact UVNext.CouplingReset.flags_one _
   exact (norm_nonneg _).trans (hm.valid 0 (by rw [norm_zero]; linarith) hp [] (by simp) (by simp))
lemma shelter (U:Pier c G W x μ L Q A η β χ α) (h:Funk.Treasury (G:=G) (L:=L) K Λ Y B β x)(he:Funk.Pier.Materia Q Λ χ U B)(hp:Funk.Pier.Enrollment Q K Λ Y χ U B) (a:α) : 0 ≤ Funk.wages' Λ Y B β x:=by
   obtain ⟨S,hS⟩:= Funk.Pier.barns Q K Λ Y h he hp
   let t: Pier.Cuts Q χ U:= ⟨S.A.filter fun i=> i∈Pier.pays Q U,S.B.filter fun i=> i∈ U.owes⟩
   have hx : Pier.Cuts.Above Q S t:= ⟨fun _ hi=> (mem_filter.mp hi).2,fun _ hi=> mem_filter.mpr hi,fun _ hi=> (mem_filter.mp hi).2,fun _ hi=> mem_filter.mpr hi⟩
   exact taxV _ _ ((hS t hx|>.heard a).2) h.mores
end YM.RemainderComparison.Cadenza
