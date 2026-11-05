import YM.RemainderComparison.Cadenza.Hits
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
-- estimates harvest. Render clients multiply all `royale` coefficients by 1+|f|
-- for authentic envelopes on normalized input Pose. Doesn't hide marked.N.Source normalization.

def royale (x:ℝ) := let a:= seat p r s t E' D x; let b:= bandPay p r s t E' D x
                       (7:ℝ) + |a|+|b|+|chapter r D x|+|D.e x|

variable {v:ℝ}
lemma grand (hb:D.Financed G p.L v)(hd:0<D.d)(hz:0<D.Z): Reserve G p.L (royale p r s t E' D):=by
   have he : Reserve G p.L (chapter r D):= (((hb.balloon.pow _).mul hb.balloon).mul hb.pays)
   exact ((((Reserve.const _|>.add (seating p r s t E' D hb hz hd).absolute).add (aria p r s t E' D hb hz hd).absolute).add he.absolute).add hb.tunes.absolute)

-- Payable OPTIONAL calibration size (strong ηw or inverse period). 5 chosen.
local notation "Πx" => royale p r s t E' D
structure Summits (x β:ℝ) (f:ℝ→ℝ) (η δ:ℝ): Prop where
   gains : 0 < Πx x
   heat : (1+|f x|)*Πx x ≤ (gStep β)^(-η)
   shade : (gStep β)^(r.p+1)* (1+|f x|)*(Πx x) ≤ (gStep β)^ (((r.p+1:ℕ):ℝ)-η)
   owed : |D.herd x| ≤ δ
   admits (v:ℝ) : 0≤v → v≤ (gStep β)^5→ D.Y x*v≤1∧ Lyric.tax G p.L x*v≤1

variable (hd:0<D.d)(hz:0<D.Z){qZ β δ:ℝ}
include hd hz
lemma expedites (hb:D.Financed G p.L qZ)(f:ℝ→ℝ)(η δ:ℝ)(ht:Reserve G p.L f)(hη:0<η)(hδ:0<δ): ∀ᶠ x in atTop, ∀ β,inBand (betaF G x p.L) β→ Summits p r s t E' D x β f η δ := by
   let h:= ((Reserve.const 1).add ht.absolute).mul (grand p r s t E' D hb hd hz)
   let a:= Access.apron G p.L; have he:= Access.rates_apron (G:=G) (L:=p.L)
   have hy:= ((hb.balloon.absolute).rate.mul (he.pow 5)).below (by norm_num) _ zero_lt_one
   have hK : Rate G p.L (3/8*(5:ℕ):ℝ) (Lyric.tax G p.L):= (Rate.power (G:=G) (L:=p.L) (a:=3/8)).pow 5
   have hh:= ((Brim.absolut hK).mul (he.pow 5)).below (by norm_num) _ zero_lt_one
   obtain ⟨q,hq,hH⟩:= hb.colder
   filter_upwards [Access.wide hb.balloon.rate, hy,hh,hH.below hq δ hδ, Access.burn hη h.rate, Access.pay η hη h (r.p+1)] with x hP hW hZ hx he₀ he₁ β hβ
   have hg : 0<Πx x:=by unfold royale; positivity
   have hN : 0< (1+|f x|) * (Πx x):=by positivity
   have hA := hP.2 β hβ
   refine ⟨hg,(le_abs_self _).trans (he₀ β hβ),le_trans ?_ (he₁ _ hβ), hx,fun v hv hp=>?_⟩
   · rw [abs_of_pos hN,mul_assoc]
   exact ⟨le_trans (mul_le_mul (le_abs_self _) (hp.trans (pow_le_pow_left₀ hA.1.le hA.2.le 5)) hv (abs_nonneg _)) ((le_abs_self _).trans hW),le_trans (mul_le_mul (le_abs_self _) (hp.trans (pow_le_pow_left₀ hA.1.le hA.2.le 5)) hv (abs_nonneg _)) ((le_abs_self _).trans hZ)⟩
omit hd hz

-- scope interpolation: projection budget base is analytic, all inherited REAL.Qt.Representative estimates. No unmask gain for wind.E.
lemma totals (f:ℝ→ℝ)(δ:ℝ) (h: Summits p r s t E' D x β f η δ)(hβ:0≤gStep β)(ε U C₀:ℝ)(he:0≤ε)(hu:0≤U) :
      let g:=(gStep β)^(r.p+1)
      let dA:=g*(seat p r s t E' D x)
      let bA:=g*(bandPay p r s t E' D x)
      let e₁:= D.e x* U; let e₂:= chapter r D x * ε; let F':=1+|f x|
      (dA+(7*g+(C₀/p.L.val+D.herd x)*U+e₂) ≤ (C₀/p.L.val+δ)*U + Πx x*g + Πx x * ε)
       ∧ (bA+(7*g+e₁+e₂) ≤ Πx x*(g+(ε+U))) ∧
       F'* (bA+(7*g+e₁+e₂)) ≤ (gStep β)^(((r.p+1:ℕ):ℝ)-η)+F'*Πx x*(ε+U):=by
   intro g d b e₁ e₂ F'; have hg:0≤g:=pow_nonneg hβ _
   let F:=Πx x; have hD : seat p r s t E' D x + 7 ≤ F:= by
      have hp:=le_abs_self (seat p r s t E' D x); unfold F royale; linarith [abs_nonneg (chapter r D x),abs_nonneg (D.e x),abs_nonneg (bandPay p r s t E' D x)]
   have hc : chapter r D x ≤ F:=by unfold F royale; linarith [le_abs_self (chapter r D x), abs_nonneg (seat p r s t E' D x),abs_nonneg (D.e x),abs_nonneg (bandPay p r s t E' D x)]
   have he': D.e x ≤ F:=by unfold F royale; linarith [le_abs_self (D.e x),abs_nonneg (seat p r s t E' D x),abs_nonneg (chapter r D x),abs_nonneg (bandPay p r s t E' D x)]
   have hb : bandPay p r s t E' D x+ 7 ≤ F:=by unfold F royale; linarith [le_abs_self (bandPay p r s t E' D x),abs_nonneg (seat p r s t E' D x),abs_nonneg (chapter r D x),abs_nonneg (D.e x)]
   have hC : e₂ ≤ F* ε:=mul_le_mul_of_nonneg_right hc he
   have he'' : e₁ ≤ F* U:=mul_le_mul_of_nonneg_right he' hu
   have hx : b+(7*g+ e₁+e₂)≤ F*(g+(ε+U)):=by unfold b; nlinarith only [mul_le_mul_of_nonneg_right hb hg,hC,he'']
   change (d+_ ≤ _+F*g+F*ε) ∧ ( _≤ F*_) ∧ F'*_ ≤ _+F'*F*(ε+U)
   refine ⟨?_,hx,?_⟩
   · have H: D.herd x ≤ δ:= (le_abs_self _).trans h.owed
     unfold d; nlinarith only [mul_le_mul_of_nonneg_right H hu,hC, mul_le_mul_of_nonneg_right hD hg]
   apply (mul_le_mul_of_nonneg_left hx (show 0 ≤ F' by unfold F'; positivity)).trans; rw [← mul_assoc,mul_add, ← add_zero ((gStep β)^(((r.p+1:ℕ):ℝ)-η)),add_zero]; apply add_le_add_left _ _; rw [mul_comm _ g,← mul_assoc]; exact h.shade
end YM.RemainderComparison.Cadenza
