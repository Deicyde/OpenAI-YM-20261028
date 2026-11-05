import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Riddle
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Rope
/-!
 # Program.pre proof components.Prepared recipes for H24.Bind.C.With.K Θ forecast.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Tablet Quill Baffle Prism Brim Lotus Peak Greenbelt WardBin.Lies March
open Gas Ursell Trees Daisy Daisy.Charity
open Lute
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
    {B B' : BudgetPoint} {Y : Support c} {K : Support f} {U : Config G c} {W μ x C' : ℝ} {R : Rep G f}
    {p j n m k : ℕ} {L : Side} {Q: ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable {d A t C w M N z β r η v b Y' q e: ℝ}{C₀ : Libretto G n}

section record
-- harvest.Of powers AFTER B.Vertex. both.
def priceA (p d r:ℕ)(B A M Z:ℝ)(Q : Rights G n):Prop := ∀ (c f:Side)(S: StepData c f)(C: Libretto G n)(D: Record)(K J:BudgetPoint)(X:Support f)(Y:Support c)(u x:ℝ), K.power=p → J.supportExponent=B → Release.accepts r B A S.patch.L → Walled S X Y x r → K.B=radiusB x → J.B ≤ 2*K.B → K.threshold ≤ 2*J.threshold → 0≤u → Peak.Rented d C D K J S.patch.L r x u → ∀ τ:ℝ,0≤τ → Real.exp (A*coverNumber K.B Y)*(τ * Peak.sale d Q C M D K J S.patch.L X r x u) ≤ Z*((S.patch.L.val:ℝ)⁻¹)^(d+1)*J.mass X τ
def priceB (p d r:ℕ)(B A Z:ℝ) (C:Libretto G n):Prop:= ∀ (c f:Side)(S:StepData c f)(D:Record)(K J:BudgetPoint)(X:Support f)(Y:Support c) (u x:ℝ), K.power=p → J.supportExponent=B → Release.accepts r B A S.patch.L → Walled S X Y x r → K.B=radiusB x → J.B ≤ 2*K.B → K.threshold≤2*J.threshold → 0≤u → Lute.Plented C D K J S.patch.L r x u → ¬ Short S J X → ∀ τ:ℝ,0≤τ → Real.exp (A * coverNumber K.B Y)*(τ*Lute.returnFee C D K J S.patch.L X r x u) ≤ Z*((S.patch.L.val:ℝ)⁻¹)^(d+1)*J.mass X τ
end record
variable (H : Cash W x μ L Q o C T R)(f' : Lotus.Leaf R) (i : ℕ)(hx:f'.turn=.logKey i)
variable (D : Record)(κ q':Chi)(ε:ℝ)(hN: Captain H p C' d v t A b r M q m Chi.canonical) (hR:Herd H hN.conduit A M m)
variable (L' : Config G f→ℝ)(h':R.p.Regular (R.activities.reg i).support L')(hm:f'.ingredient=masked R.p.threshold (R.activities.reg i).support L')
    (hp:Plays C₀ D B R.p P T x) (hz:z≥0)
    (hv: PermitY Q C₀ D B.power W o κ μ x z L)
    (hB:B.B=radiusB x)(hn:B.order≤p) (hq:Q.halo+5≤k) (hh: coverNumber B.B (plate H i).support ≤ B.B)
set_option quotPrecheck false
local notation "o₀"=>(plate H i).support
local notation "v₀"=>(plate H i).site
local notation "d₀"=>(R.activities.reg i).support
local notation "τ"=> f'.weight
variable {α m₀ q₀ : ℝ}{ℓ:ℕ}(h₁:R.p.supBounds (R.activities.reg i).site (R.activities.reg i).support L' f'.weight)(hW:Release.accepts k R.p.supportExponent (B.supportExponent+2) S.patch.L)
-- tally arc price
include hh
include hp h' hx hm hv hz hB hn hq h₁ hR
lemma hinges (K:Rights G n)(hs:Short S R.p d₀)(hr: lit (R.activities.reg i).site d₀ L' ℓ)(hO:ℓ+1≤n) (hT: Peak.glider G T ℓ R.p.power (2*C₀.C) m₀) (hm₀:1≤ m₀) :
    B.supBounds (plate H i).site o₀ (matin f' H (icon H i) Chi.canonical) (τ*Peak.sale ℓ K C₀ m₀ D B R.p S.patch.L d₀ k x (gStep R.beta)+τ*z):=by
    have hg:0<gStep R.beta:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
    have hxQ : 0≤ Peak.sale ℓ K C₀ m₀ D B R.p S.patch.L d₀ k x (gStep R.beta):=by
       unfold Peak.sale; have he:=Peak.polepos ℓ K (zero_le_one.trans hm₀); have hp:= wage_pos ℓ C₀ D B R.p S.patch.L d₀ k x (gStep R.beta) hg.le
       have hk := D.peak
       unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity
    apply around H f' i hx D κ Chi.canonical 1 hN hR L' h' hm hp hv hB hn hh hz (mul_nonneg f'.profit hxQ)
    intro V hV F g l hl hx
    exact Peak.tinyBill Chi.canonical 1 g (mapcase H i F) 1 hp h' (R.activities.reg i).anchor (billboard H hq i) hg.le (guard_silent κ hg (mul_pos D.guards R.p.threshold_pos)) hV h₁ hs hO hT hm₀ hr K l hl hx
lemma flood (hs:¬Short S R.p d₀) : B.supBounds (v₀) o₀ (matin f' H (icon H i) Chi.canonical) (τ *Lute.returnFee C₀ D B R.p S.patch.L d₀ k x (gStep R.beta)+τ*z):=by
    have hg:0<gStep R.beta:=inv_pos.mpr (Real.sqrt_pos.mpr H.laws.intake.positive)
    have hxQ : 0≤ Lute.returnFee C₀ D B R.p S.patch.L d₀ k x (gStep R.beta):=by
       unfold Lute.returnFee; have he:=beat_nn C₀; have hp:= rust_nn (r:=k) (C:=C₀) (D:=D) (P:=B) (B:=R.p) (x:=x) (L:=S.patch.L) (X:=d₀) hg.le
       have hk:=D.peak; have hb:0≤ Lute.decay R.p S.patch.L d₀:=Lute.decay_pos.le
       unfold AnalyticBridge.LocalGaussian.Moments.meter AnalyticBridge.LocalGaussian.Moments.inflate; positivity
    apply around H f' i hx D κ Chi.canonical 1 hN hR L' h' hm hp hv hB hn hh hz (mul_nonneg f'.profit hxQ)
    intro V hV F g l hl hx
    exact Peak.huge Chi.canonical 1 g (mapcase H i F) 1 hp h' (R.activities.reg i).anchor (billboard H hq i) hg.le (guard_silent κ hg (mul_pos D.guards R.p.threshold_pos)) hV h₁ hs l hl hx
-- Halo compression for remainder charge.
include hW
omit hp h' hx hm hv hn h₁ hR hh hz
lemma fades (hs : R.p.B ≤ 2*B.B)(z:ℝ)(hz : 0≤z) :
    Real.exp ((B.supportExponent+2)*coverNumber B.B o₀)*(z*f'.weight) ≤ Real.exp (Heir.Release.base (B.supportExponent+2) k)*z*R.p.mass (R.activities.reg i).support f'.weight:=by
  have hp:= B.exponent_pos; have h:= Heir.Release.compressed (by positivity : 0≤ B.supportExponent+2) hW (billboard H hq i) hB hs
  let g := R.p.supportExponent; let a:ℝ:= coverNumber R.p.B (R.activities.reg i).support
  have ht: g≥0:= R.p.exponent_pos.le; have ha:0≤a:=Nat.cast_nonneg _
  have hc:(B.supportExponent+2)*coverNumber B.B o₀ ≤ Release.base (B.supportExponent+2) k+g*a:=h.trans (by linarith [mul_nonneg ht ha])
  refine (mul_le_mul_of_nonneg_right (Real.exp_monotone hc) (mul_nonneg hz f'.profit)).trans_eq ?_; rw [Real.exp_add]; unfold BudgetPoint.mass; unfold g a; ring
end YM.PhysicalNext.Repeat.Mercury
