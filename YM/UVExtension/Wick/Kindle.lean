import YM.UVExtension.Lamppost.Tone
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Pattern

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
/-- actual inverse coupling (=hatted scale only for installed thresholds) -/
def flight (R : RG.Rep G f) (b : ℝ) := {R with beta:=b}
def scaled (v : ℝ) (z : Air f G) := (gStep v)⁻¹ • z
lemma scaled_tip (z : Air f G) (v : ℝ) (i): scaled v z i=(gStep v)⁻¹*z i := rfl
lemma gust (w : Air f G) (h : 0<v) : X.liftA v (scaled v w) = X.μ+ X.atmos w := by
  unfold liftA; have he : X.atmos (scaled v w)=(gStep v)⁻¹ • X.atmos w:=rfl; rw [he,smul_inv_smul₀]; exact (inv_pos.mpr (Real.sqrt_pos.mpr h)).ne'
lemma fanned (w : Air f G) (h : 0<v) : worldZ X v (scaled v w)=voltage X+X.atmos w := by
  unfold worldZ; have he : X.atmos (scaled v w)=(gStep v)⁻¹ • X.atmos w:=rfl; rw [he,smul_inv_smul₀]; exact (inv_pos.mpr (Real.sqrt_pos.mpr h)).ne'
lemma qratio (h : 0<u) : (gStep u)⁻¹*(gStep u)⁻¹=u := by rw [gStep,inv_inv,Real.mul_self_sqrt h.le]
lemma qglows (h : 0<u) (i : Bond f) : qlinear X u (scaled u z) i=u * qlinear X 1 (scaled 1 z) i := by
  unfold qlinear; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; let p:=X.plate *ᵥ X.driftM+X.linearBill
  change scaled u z _*(-(gStep u)⁻¹*p _)=u* (scaled 1 z _*(-(gStep 1)⁻¹*p _)); rw [scaled_tip,scaled_tip (v:=1)]; have he : gStep 1=1:= by norm_num [Coat.gStep]
  have hp:= qratio h; rw [he, inv_one, one_mul]; linear_combination -z (i,x)*p (i,x)*hp
lemma vapours (h : 0<u) (i : Ledger f 2) : qunique X (scaled u z) i=u*qunique X (scaled 1 z) i := by
  unfold Coat.qunique Coat.circle; dsimp only; rw [mul_left_comm u]; apply congr_arg (fun t:ℝ=> (1/2:ℝ)*t); rw [Finset.mul_sum]; apply sum_congr rfl; intro x _; rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum]
  apply sum_congr rfl; intro j _
  let V:=combo i.2.1 i.2.2 (X.finale i.1) x j; let k:=(arrive i.2.1 i.2.2,j)
  change scaled u z _*(V * scaled u z k) = u * (scaled 1 z _ * (V * scaled 1 z k)); simp only [scaled_tip]
  rw [show gStep 1=1 from by norm_num [Coat.gStep], inv_one, one_mul,one_mul]; linear_combination z (i.2.1,x)*V*z k*qratio h
lemma majorg (y : Directions G f) (h : 0<u) (i : Bond f) : major X a (flight R u) y (scaled u z) i=u * major X a (flight R 1) y (scaled 1 z) i := by
  unfold Polar.major; rw [mul_left_comm u]; congr 1; rw [Finset.mul_sum]; apply sum_congr rfl; intro x _; let p:= X.plate *ᵥ well X+leanB X
  change scaled u z _*((-(gStep u)⁻¹)*p _)=u* (scaled 1 z _*((-(gStep 1)⁻¹)*p _)); rw [scaled_tip,scaled_tip]; rw [show gStep 1=1 from by norm_num [Coat.gStep],inv_one,one_mul]; linear_combination -z (i,x)*p (i,x)*qratio h

-- split inherits payoff comparators. We don't spend real conditional law's numerator twice.
def betaBit : LogIndex c f→Bool := Sum.elim
    (Sum.elim (fun _=>false) (Sum.elim (fun _=>true) (Sum.elim (fun _=>true) (Sum.elim (fun _=>false) (Sum.elim (fun _=>true) (fun _=>true))))))
    (Sum.elim (Sum.elim (fun _=>true) (fun _=>false)) (Sum.elim (fun _=>false) (Sum.elim (fun _=>false) (Sum.elim (fun _=>false) (fun _=>true)))))

def exposure (s : ℝ) (i : LogIndex c f) := if betaBit i then s else 1
lemma quoted (h : 0 < u) (i : LogIndex c f) :
    farLog X (flight R u) a Z (scaled u z) i=exposure u i * farLog X (flight R 1) a Z (scaled 1 z) i := by
  have he:0<(1:ℝ):=zero_lt_one
  unfold farLog exposure; dsimp only [flight]; rw [gust _ _ h,gust _ _ he]
  rcases i with (i|i|i|i|i|i) | ((i|i|i)|(i|i|i|i|i))
  all_goals simp only [betaBit, ↓reduceIte, Bool.false_eq_true,Sum.elim, Coat.fuel, inhale, expo, translateValue, pairValue,Short, one_mul] -- giant
  all_goals first | rfl | (unfold speck; split <;> ring) | (rw [Coat.qfirst,Coat.qfirst,qglows _ h]; unfold aperture; rw [gust _ _ h,gust _ _ he,mul_left_comm]) | (rw [Coat.chain,Coat.chain,vapours _ h]; unfold aperture; simp_rw [gust _ _ h,gust _ _ he]; ring) | (ring_nf; rfl)
lemma recess (y : Directions G f) (U : Config G f) (h : 0<v) (i : LogIndex c f) :
    logMoment X a (flight R v) Z y U (scaled v z) i=exposure v i* logMoment X a (flight R 1) Z y U (scaled 1 z) i := by
  unfold Polar.logMoment exposure
  rcases i with (i|i|i|i|i|i)|((i|i|i)|(i|i|i|i|i)); all_goals simp only [betaBit,Bool.false_eq_true, ↓reduceIte,Sum.elim, frost, nest, whelp, spins,translateValue,pairValue,icicle,one_mul]
  all_goals first | exact majorg X y h i | rfl | (unfold entangled; rw [vapours _ h,mul_left_comm]) | (simp only [Polar.hover,flight]; split_ifs <;> ring) | (unfold flight; ring_nf; rfl)
end YM.UVExtension.Wick
