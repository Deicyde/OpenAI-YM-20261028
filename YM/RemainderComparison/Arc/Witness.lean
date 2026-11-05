import YM.RemainderComparison.Arc.Pad

/-!
 # Shared aperture compiler and quantitative `Region` interface to representation owner.

 * Stimulus: readiness threshold PER uptake setup and expansion parameters.
   Not asserting the current varying calendar satisfies all such delays!
 * Region: per-supplier in same aligned layout. RG03 arranging equality
   across actual letter sets can consume even a finite selection of these pads,
   then ordinary budget sums. Effective stencil budget at full inflated mask,
   P.order may be that of the post estimator (not just external probes).
 * No inference from reduced mass back on unsupported V. RG02 must identify
   model in X variables (including β-reset convention) with formal kernels.
   Their analytic discrepancy on these charts if using cutoff transfer can
   use the `connector` slot; not bundled here with main analytic production.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Arc
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux
open YM.RemainderComparison.Exchange
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f L : Side} {j w k W Y κ : ℕ} {P:BudgetPoint} {A p R b x : ℝ}
variable {v : Positions (Uniform.Primary c G)}
variable {g h : ℝ→ℝ}

structure Stimulus (G : Gauge) (L : Side) (x : ℝ) (r : ℝ) (j Y : ℕ) : Prop where
  rich : 1 ≤ r
  light : 0 < furl G L x ∧ furl G L x < r
  angle β : inBand (betaF G x L) β → gStep β*(2*r)< eaves G L x
  contract (β:ℝ) (P:BudgetPoint): inBand (betaF G x L) β → P.threshold=Pressure.temp x → P.threshold ≤ 2*Pressure.fiery G x L → P.order=j → Tracer P G β r ∧ Deduct G P β Y r
lemma finance (G : Gauge) (L : Side) (Y : ℝ→ℕ) (h: Reserve G L (fun x=>(Y x:ℝ))) (j : ℕ) :
    ∃ p:ℝ→ℝ, Reserve G L p ∧ ∀ᶠ x in atTop, Stimulus G L x (p x) j (Y x) := by
  obtain ⟨A,hA,H⟩:=Arc.threshold Y h
  obtain ⟨r,hr,hR⟩:= Arc.coverage G L j A hA
  refine ⟨r,hr,?_⟩; filter_upwards [hR,H] with x hx hh
  obtain ⟨ha,hv,hφ,hc,hK⟩:=hx; exact ⟨ha,⟨hv,hφ⟩,fun β hb=> (hK β hb).1,fun β P hb hp hk hi=> ⟨(hK β hb).2 P hp hk hi,(hh P β hb hk).enlarge ((le_abs_self _).trans hc)⟩⟩

-- `K` integer real width compiler. prepare per finite-orders request.
def couponCost (j k Y:ℕ) (R:ℝ) := 2^j*((1+(Y:ℝ))^(k*j))* Arc.budgetizer j R 1
def landed (j k κ Y:ℕ) (R E : ℝ) := Real.exp (E*((κ+κ+1:ℕ)^4:ℕ))*couponCost j k Y R
lemma coupon_every (j k:ℕ) {Y:ℝ→ℕ} (hr : Reserve G L g) (h: Reserve G L (fun x=>(Y x:ℝ))) : Reserve G L fun x=> couponCost j k (Y x) (g x) :=
    (Reserve.mul (Reserve.const _) (((Reserve.const _).add h).pow _)).mul (fee_rate hr (Reserve.const _))
lemma landed_every (j k κ : ℕ) {Y:ℝ→ℕ} (E:ℝ) (hr : Reserve G L g) (h: Reserve G L (fun x=>(Y x:ℝ))) : Reserve G L fun x=> landed j k κ (Y x) (g x) E:= Reserve.mul (Reserve.const _) (coupon_every j k hr h)

section pad
variable (p:2*w ≤ f.val) (hp:w+1 ≤ Y) (hd : Deduct G P b Y R)
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
variable (o:Site c) (f₁: Config G f→E) (hg: P.Regular univ f₁)
local notation "U" => f₁ ∘ shape (Slide.cognac p) o
lemma viewM (ht : Y ≤ κ*P.B) : coverNumber P.B (neighbors Y o) ≤ (κ+κ+1)^4:=
    (Corona.cover_mono (Corona.halo_mono ht (Finset.Subset.refl {o})) P.B).trans (Corona.tile o κ P.B P.B_pos)
include hg hd hp
lemma harvest (hx : 2*Y < c.val) (h : Tracer P G b R) (hr:1 ≤ R) (ht:Y ≤ κ*P.B) {D:ℝ} (hC:P.supportExponent ≤ D) (hh:0≤A) (hQ:∀ v:Positions (Uniform.Primary f G), ‖v‖ ≤ R → Arc.route G b v∈Boulevard.sunny P → Brush P.order A 1 (f₁ ∘ Arc.route G b) v) :
    let q:= couponCost P.order P.power Y R
    P.Regular (neighbors Y o) U ∧ P.supBounds o (neighbors Y o) U (A*q) ∧ P.mass (neighbors Y o) (A*q) ≤ A* landed P.order P.power κ Y R D := by
  intro q
  have ht':= viewM o ht
  have hf := deductive hx h hd (k':=p) o f₁ hp hg hr hh hQ
  have hq:Trio.tilt P Y* Arc.budgetizer P.order R A=A*q := by unfold q Arc.budgetizer Trio.tilt couponCost Boulevard.ticket budgetizer Boulevard.ticket; ring
  refine ⟨ regular (p:=p) o hp hg, hq ▸ hf, ?_⟩
  unfold BudgetPoint.mass; refine (mul_le_mul_of_nonneg_right (Real.exp_monotone (show P.supportExponent * _ ≤ D * ↑((κ+κ+1:ℕ)^4) from ?_)) (show _ from hq ▸ hf.1)).trans_eq ?_
  · exact mul_le_mul hC (by exact_mod_cast ht') (Nat.cast_nonneg _) (P.exponent_pos.le.trans hC)
  unfold landed q couponCost; ring

variable [CompleteSpace E] [SecondCountableTopology E]
-- proving patch matching includes realignments; pay f's transfer also here.
/-! `F` not implicitly dropped even if f₁ is a difference of evaluated
    densities. Supply re-expression and UV-tag equality (plus kernel cost slots).
    Any scalar/change normalization placed outside needs its own transfer control. -/
def Jurisdiction (f : Side) (A K b r:ℝ) (P:BudgetPoint) (i:ℕ) (f₁: Config G f→E): Prop:= ∀ p:Positions (Uniform.Primary f G), ‖p‖ ≤ r → Arc.route G b p ∈ Boulevard.sunny P →
    ∃ (U₀:Positions (Uniform.Primary f G)→E) (W:ℝ × Positions (Uniform.Primary f G)→E) (u v:ℝ) (w : Positions (Uniform.Primary f G)→E), Queue W U₀ (gStep b) p v u P.order i A ∧ Brush P.order K 1 w p ∧
      ∀ᶠ x in 𝓝 p, f₁ (Arc.route G b x)= U₀ x - Trace.trunc i W (gStep b,x)+w x
variable {t C e:ℝ} {m : ℕ}
-- `Carries` kernel etc from Aux.horizon when synchronized; w residual e.g. correction from spatial-cut comparison. Exact scope at one root o.
lemma ceded (hx : 2*Y < c.val) (h : Tracer P G b R) (hr:1 ≤ R) (ht:Y ≤ κ*P.B) {D:ℝ} (hC:P.supportExponent ≤ D) (hz:0 ≤ A) (hf:0≤t) (hb:0<b) (he: Jurisdiction (E:=E) f A ((gStep b)^(m+1)*t) b R P m f₁):
    let s:=gStep b; let u:=s^(m+1)*(A+A+t)
    P.Regular (neighbors Y o) U ∧ P.supBounds o (neighbors Y o) U (u*couponCost P.order P.power Y R) ∧ P.mass (neighbors Y o) (u*couponCost P.order P.power Y R) ≤ u* landed P.order P.power κ Y R D := by
  intro s u
  have hp' :0<s:= (Fare.gS _ hb).1
  refine harvest p hp hd o f₁ hg hx h hr ht hC (by unfold u; positivity) ?_
  intro v hv ht; obtain ⟨U',W,v,g,w,hV,hW,hw⟩:= he _ hv ht
  have h:= hV.projects.gathering hW
  unfold u; rw [mul_add]; exact h.shimmy hw
end pad
end YM.RemainderComparison.Arc
