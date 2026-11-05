import YM.RemainderComparison.Cadenza.Curd
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
namespace Expenditure
open WickReps Trio
local notation "W'" => E'.order
local notation "P'" => E'.power
local notation "Z'" => t.z
local notation "U'" => t.halo
local notation "K'" => t.k
local notation "J" => s.post D.d D.Z D.R D.charge

open Flues
local notation "X"=> fun x:ℝ=>D.Rb x -- argument
local notation "V"=> s.unsigned
local notation "bC"=>bandPay p r s t E' D
local notation "W"=>s.kernel

def chapter (x:ℝ):= D.Y x^r.k* D.Y x*D.spin x

def playS (x:ℝ):= D.Y x^r.k* D.spin x

def autumn (x β v:ℝ):ℝ:= gStep β^(r.p+1)*bandPay p r s t E' D x + Manor.tribute t.ℓ (t.k x) (r.σ+1) ((ballCost (t.halo x)) * (playS r D x+ chapter r D x*v+s.B x))

def incline (x:ℝ) := |bandPay p r s t E' D x| + Manor.tribute t.ℓ (t.k x) (r.σ+1) ((ballCost (t.halo x))* (playS r D x+ |chapter r D x|+ s.B x))
lemma prize {β v:ℝ}(h: Temper B E' x G p.L)(hp:gStep β≤1)(hv:0≤v)(hz:v ≤1): autumn p r s t E' D x β v= WickReps.burse B (t.k x) (t.z x) (Funk.wages' (D.layer p s t E' r x) (D.gold x) B β x)*Manor.tribute t.ℓ (t.k x) (r.σ+1) (Breeze.areaBudget (t.halo x) r.k (s.kernel x))+Manor.tribute t.ℓ (t.k x) (r.σ+1) ((ballCost (t.halo x))*(((D.Y x^r.k*D.spin x+D.Y x^r.k*D.Y x*D.spin x*v)+s.B x))) ∧ autumn p r s t E' D x β v ≤ incline p r s t E' D x:=by
   constructor
   · unfold autumn; rw [← (shares p r s t E' D h β).2]; rfl
   have hh: 0≤gStep β:= inv_nonneg.mpr (Real.sqrt_nonneg _)
   have hf: chapter r D x*v ≤ |chapter r D x|:= (mul_le_mul_of_nonneg_right (le_abs_self _) hv).trans (mul_le_of_le_one_right (abs_nonneg _) hz)
   exact add_le_add ((mul_le_mul_of_nonneg_left (le_abs_self _) (pow_nonneg hh _)).trans (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hh hp))) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (add_le_add_right hf _) _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)) (Real.exp_nonneg _))
variable {v a b u d y z γ v' b' d' Q':ℝ}
lemma Resonant'.mono (h : Flues.Resonant (radiusB x) j v b d r.σ u a y z) (he:v'≤v)(ha:b'≤b)(hf:d'≤d): Flues.Resonant (radiusB x) j v' b' d' r.σ u a y z:={ h with
    small:=he.trans h.small
    joint:= (add_le_add (mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr h.gain.le)) (add_le_add (mul_le_mul_of_nonneg_left he zero_le_two) (mul_le_mul_of_nonneg_left hf (inv_nonneg.mpr (zero_le_one.trans h.shrink))))).trans h.joint }
variable {qZ:ℝ}(hD:D.Financed G p.L qZ)(hz:0<D.Z)(hd:0<D.d)
include hD hz hd
lemma inclined : Reserve G p.L (incline p r s t E' D):=by
   have ht := ((hD.balloon.pow r.k).mul hD.balloon).mul hD.pays
   exact (aria p r s t E' D hD hz hd).absolute.add (Expenditure.tribute _ _ t.keeled ((Reserve.ball _ t.board).mul ((((hD.balloon.pow _).mul hD.pays).add ht.absolute).add s.hope)))
omit hD hz hd
structure Harmonious (x β:ℝ)(Z:BudgetPoint):Prop where
   resonance (Y:Stars→Side) : (∀ i:Stars,(Y i).val=2*(t.n x+i.val)) → ∀ v:ℝ,0≤v → v≤1 →
      ∃ w u y:ℝ, Flues.Resonant Z.B r.k (paymentB (t.halo x) (t.k x) t.ℓ Y (D.Rb x+s.unsigned x) (D.Rb x) (s.unsigned x) (r.σ+1)) (Lyric.unitK x^4*gStep β^r.s) (autumn p r s t E' D x β v) r.σ (Lyric.unitK x^4*gStep β^r.finalG) w u y

include hD hz hd
lemma swings (q:ℝ)(h:r.Heart E' q)(hr:qZ<0): ∀ᶠ x in atTop,∀ Z:BudgetPoint,Temper Z E' x G p.L →∀ β,inBand (betaF G x p.L) β→ Harmonious p r s t E' D x β Z:=by
    let z:=max qZ s.rate; have hh:=salary' p r t D.Rb s.unsigned z (hD.low.weaken (le_max_left ..)) (s.stage.weaken (le_max_right ..))
    have he:= Flues.funding (Expenditure.signed p r t D.Rb s.unsigned) _ hh (max_lt hr s.night) (inclined p r s t E' D hD hz hd).rate h.stores r.k r.finalG
    filter_upwards [he,Access.wide (Rate.const (G:=G) (L:=p.L) 1)] with x hx hZ Z hp β hβ; constructor; intro Y hY v hv hv'
    obtain ⟨w,u,y,hN⟩:= hx _ hβ
    rw [hp.pose]; refine ⟨w,u,y,Resonant'.mono r hN ((remits p r t D.Rb s.unsigned x hY).trans_le (le_abs_self _)) ?_ ?_⟩ -- order
    · have hh : gStep β≤1 := (hZ.2 β hβ).2.le.trans (hZ.1.2.1.le.trans hZ.1.2.2.1.le)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (hZ.2 β hβ).1.le hh (show r.finalG+1 ≤ r.s from h.atHull)) (pow_nonneg (cheap x|>.1.le) _)
    exact ((prize p r s t E' D hp (show gStep β≤1 from (hZ.2 β hβ).2.le.trans (hZ.1.2.1.le.trans hZ.1.2.2.1.le)) hv hv').2).trans (le_abs_self _)
end Expenditure
end YM.RemainderComparison.Cadenza
