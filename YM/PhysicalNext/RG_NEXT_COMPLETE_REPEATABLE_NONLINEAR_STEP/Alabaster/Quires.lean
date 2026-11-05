import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Tower
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Alabaster.Beet
/-! # Monograms. Truly moving β even inside the seed stencils.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Alabaster
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Shell Channel Oriented SliceRows Control Window Census Green Mask Pulse Itinerary Coat
open Packets Presented LabelSum Sector SliceRows.DataKernel LocalRows Footprint Raw ProbabilityTheory Poll Pond Matter
open Blaze Silica Scroll Vine Stained Polar Shield Flux Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable (a W : ℝ) {R R' : RG.Rep G f} (P : Facing R R') (O : ChartRatio G)
    (X : Coat T F) (k : Finset ℕ) (z : Air f G) (U : Directions G f) (V : Config G f)
local notation "L" => low R R'
include P
lemma charged : Contract.order R k= Contract.order R' k:= by unfold Contract.order Contract.charges Contract.covered; rw [P.forced,P.params]
lemma alarmWhistle (i : WarningAt c f) : Polar.sprinkle X a R W U V k i=Polar.sprinkle X a R' W U V k i:= by unfold Polar.sprinkle Polar.flare Polar.veil Contract.charges Contract.covered; rw [P.params,P.forced]
lemma alarmLace (i : WarningAt c f) : X.detect (X.liftA R.beta z) W a R k i=X.detect (X.liftA R'.beta (L • z)) W a R' k i := by
  rw [lifting P]; exact alarmWhistle _ _ P X k _ _ i
lemma stockMoon (A : Stores S) :
    let q:= -(R'.beta-R.beta)*(chalky X U V A+ crispy X A)- (X.pens A).card*(Real.log (measure_g O R'.beta)-Real.log (measure_g O R.beta))
    Polar.stock X a R' W O U V k A=Polar.stock X a R W O U V k A * Real.exp q := by
  intro q; unfold Polar.stock; split
  next => rw [← charged P]; rw [show Polar.plumeLog X a R' O U V A=Polar.plumeLog X a R O U V A+q by unfold plumeLog q; ring]; rw [Real.exp_add]; ring
  rw [zero_mul]
lemma risingMoon (A : Stores S) :
    let q:= -(R'.beta-R.beta)*(X.quoteNear A U+ X.far_bills A)- (X.pens A).card*(Real.log (measure_g O R'.beta)-Real.log (measure_g O R.beta))
    X.Pack R' O k W a A U=X.Pack R O k W a A U * Real.exp q:= by
  intro q; unfold Pack; split
  next => unfold steam; dsimp only; rw [← charged P]; rw [show X.steamLog R' O a A U=X.steamLog R O a A U+q by unfold steamLog q; ring]; rw [Real.exp_add]; ring
  rw [zero_mul]
lemma location (n l : ℕ) : Raw.space T l n R=Raw.space T l n R' := by unfold Raw.space regularFoot; rw [P.reg,P.path]; -- edit
lemma pointed (n l i : ℕ): forcedFoot S.ratio l n R i= forcedFoot S.ratio l n R' i:= by unfold forcedFoot; rw [P.forced]
omit P
def flips (c f : Side) (p : LogIndex c f) : Bool := match p with
   | .inl (.inr (.inr (.inr (.inl _)))) => false -- loop
   | .inl (.inr _) => true -- any other raw
   | .inr (.inl (.inl _)) => true -- Mini β speck
   | .inr (.inr (.inr (.inr (.inr _))))=> true -- Chain major or quadratic
   | _ => false
abbrev oldVac (c f : Side) (p : LogIndex c f) : Prop := ∀ i:ℕ,p≠Sum.inl (Sum.inl i)
include P
lemma hatsym : shimmer X R'.beta=L • shimmer X R.beta∧ X.hatted R'.beta=L • X.hatted R.beta:= by
  unfold shimmer Coat.hatted; rw [← smul_assoc,← smul_assoc,← ((uplift P).2.2.2.2)]; simp
omit R R' P in
lemma circleLift (i : Ledger f 2) (b : ℝ) : X.qunique (b • z) i=b^2 * X.qunique z i := by
  unfold qunique Coat.circle; dsimp only; simp only [PiLp.smul_apply,smul_eq_mul]; simp_rw [show ∀ j k l, combo i.snd.1 i.snd.2 (X.finale i.fst) k j * (b * z l)= b*(combo i.snd.1 i.snd.2 (X.finale i.fst) k j * z l) from fun _ _ _=>by ring, ← Finset.mul_sum]; rw [mul_left_comm (b^2)]; apply congrArg; rw [Finset.mul_sum]; apply sum_congr rfl; intro i _; ring
lemma glow (i : Ledger f 2) : X.chain R'.beta (L•z) a i=L^2 * X.chain R.beta z a i := by unfold Coat.chain Coat.aperture; rw [lifting P,circleLift]; ring
lemma maj (i : Bond f) : major X a R' U (L • z) i=L^2*major X a R U z i:= by
  unfold major; rw [(hatsym P X|>.1 : shimmer X R'.beta=_)]; rw [mul_left_comm (L^2)]; apply congrArg
  simp only [PiLp.smul_apply,Pi.smul_apply,mul_sum,smul_eq_mul]; exact sum_congr rfl fun i _=> by ring
lemma reel (i : Bond f) : qfirst X R'.beta (L • z) a i=L^2*qfirst X R.beta z a i:= by
  unfold qfirst qlinear aperture; rw [lifting P,(hatsym P X|>.2 : X.hatted R'.beta=_)]; rw [mul_left_comm (L^2)]; apply congrArg
  simp only [PiLp.smul_apply,Pi.smul_apply,mul_sum,smul_eq_mul]; exact sum_congr rfl fun i _=> by ring
lemma flicker (i : LogIndex c f) (h : oldVac _ _ i) : logMoment X a R' O U V (L • z) i=(if flips c f i then L^2 else 1)*logMoment X a R O U V z i:= by
  unfold logMoment; rcases i with i|i|i
  · rcases i with i|i
    · exact absurd rfl (h i)
    unfold Polar.frost; rw [← location P]; rcases i with i|i|i|i|i
    all_goals simp only [flips,↓reduceIte,Bool.false_eq_true,one_mul,nest,Sum.elim,← P.path,← P.params,← P.clip,translateValue,pairValue,icicle,← pledge P] <;> ring
  · rcases i with i|i|i<;>simp only [Polar.whelp,Sum.elim,flips,Bool.false_eq_true,↓reduceIte,one_mul]; unfold Polar.hover; rw [← pledge P]; dsimp only; split <;> ring
  rcases i with i|i|i|i|i <;> simp only [Polar.spins,Sum.elim,flips,Bool.false_eq_true,↓reduceIte,one_mul]
  · exact maj a P ..
  unfold Polar.entangled; rw [circleLift]; ring
lemma flitter (i : LogIndex c f) (h : oldVac _ _ i) : Coat.farLog X R' a O (L • z) i=(if flips c f i then L^2 else 1)*Coat.farLog X R a O z i:= by
  unfold Coat.farLog; rw [lifting P]; rcases i with i|i|i
  · rcases i with i|i
    · exact absurd rfl (h i)
    unfold Coat.inhale; rw [← location P]; rcases i with i|i|i|i|i
    all_goals simp only [flips,↓reduceIte,Bool.false_eq_true,one_mul,expo,Sum.elim,← P.path,← P.params,← P.clip,translateValue,pairValue,← pledge P] <;> ring
  · rcases i with i|i|i<;>simp only [Coat.Short,Sum.elim,flips,Bool.false_eq_true,↓reduceIte,one_mul]; unfold Coat.speck; nth_rw 1 [← pledge P]; split <;> ring
  rcases i with i|i|i|i|i <;> simp only [Coat.fuel,Sum.elim,flips,Bool.false_eq_true,↓reduceIte,one_mul]
  · exact reel a P ..
  exact glow a P ..
end YM.PhysicalNext.Repeat.Alabaster
