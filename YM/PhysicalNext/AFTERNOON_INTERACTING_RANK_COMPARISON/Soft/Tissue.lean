import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticNext.QUARTIC_MATCH.Radius.Articles
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Swatches
import YM.PhysicalNext.GRADED_QUARTIC_RATE.Stamp
import YM.PhysicalNext.SAME_SERVICE_FRESH_DETERMINANT.Orders
import YM.Primitives.TWO_WAVE_TRACE_DENSITY.Infinite
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOOP_COEFFICIENT.Block.Optimize
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching

/-!
# Value-only *ancillary* representations

 push along a comparison course. We try a different
sufficient route -- exact unnormalized densities, same coupling scale,
path & actual integration including values on flags, same support exponent
control in this representation, but the **E** terms through this stretch
are value only too: neither derivatives nor affine-pair normalization.
And we use separate numerical size estimates for them along the stretch.

This doesn't change or give any of the `Lawful` trajectories & other
original-path data required for the YM target. NOT an interpretation
of regular terms in that as value-only! In particular this is not for
getting a Program, Clocks or calibrated trajectory, nor even producing
the stronger intermediate receipt in `RankCovariance.Interaction`.
The purpose here is to still actually pay for the physical rank tests,
without requiring another *regular* shell even in the proof of *these*.

`white R` in some proof terms at the same StepData will be a temporary
calculation aid that does have Lawful. Don't confuse density application
on those arguments with the actual comparison using R.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Lattice Wilson RG Precision
open Next.Rank 
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} (R : Rep G n) {o C L q w : ℝ}

def white : Rep G n := {R with activities:={R.activities with E:=0} }

lemma noCharge : (white R).activities.RegularFamily R.p :=
  ⟨fun _=> WilsonStartup.Start.zero_reg,fun _=>rfl,fun _ _ _ _ _ _=> by simp [white,logHessian]⟩
lemma noDebit : (white R).activities.EBound R.p 0 := by
  refine ⟨fun _ => 0,fun _=> WilsonStartup.Start.zero_bound,fun i=>?_⟩
  simp only [BudgetPoint.mass,mul_zero,ite_self]
  exact ⟨fun _=>le_rfl,summable_zero,tsum_zero.le⟩

def whiteTurns (s : Signed) (b : Site n) (h : R.activities.Moves s b) : (white R).activities.Moves s b :=
  ⟨h.ep,h.kp,h.reg_site,h.reg_support,h.forced_support,h.forced_inventory,h.forced_tests,fun _ _=>rfl,h.valuesK⟩

lemma whiteGood (h : R.Lawful o C L q w) : (white R).Lawful o C L 0 w := by
  let F:= h.labels.forced
  refine ⟨h.paths, noCharge R, ⟨F.sym,F.symtest,F.meas,F.meas_test,F.reads,F.reads_test,F.permit⟩,fun a b=> ?_,noDebit R,h.labels.boundK⟩
  exact (h.labels.moves a b).map (whiteTurns R a b)

lemma whiteAdd (U : Config G n) : (white R).activities.additive R.p U=0 := by
  classical
  simp only [Activities.additive,Activities.regularOccurrence,masked,Set.indicator,white,Pi.zero_apply,ite_self,tsum_zero]

/-- Same path and scalar. -/
lemma whiteExp (U : Config G n) : R.exponent U = (white R).exponent U - R.activities.additive R.p U := by
  unfold Rep.exponent
  rw [show (white R).p=R.p from rfl,whiteAdd,sub_zero]; rfl
lemma whiteEval (U : Config G n) : (white R).eval U=Real.exp (R.activities.additive R.p U)* R.eval U:= by
  rw [Rep.eval, Rep.eval, whiteExp R,← mul_assoc,← Real.exp_add]
  exact congr_arg₂ HMul.hMul (congr_arg Real.exp (by ring)) rfl

structure Petals (q : ℝ) : Prop where
  toss i : GaugeInvariant (R.activities.regularOccurrence R.p i)
  live i : Measurable (R.activities.regularOccurrence R.p i)
  look i : UsesFinal R.p.threshold (R.activities.reg i).support (R.activities.regularOccurrence R.p i)
  price : ∃ b:ℕ→ℝ,(∀ i,0≤b i ∧ ∀ U, ‖R.activities.regularOccurrence R.p i U‖≤ b i) ∧
      ∀ x : Site n, SumBudget (fun i=> if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (b i) else 0) q

lemma petalReady (hs : R.Lawful o C L q w) : Petals R q:= by
  have hE := hs.labels.regular
  obtain ⟨b,hb,h⟩:=hs.labels.boundE
  refine ⟨fun i k U=> ?_,fun i=> masked_measurable _ _ _ (hE.smooth i).borel,fun i U V ha he=> ?_,b,fun i=>⟨(hb i).1,fun U=>?_⟩,h⟩
  · simp [Activities.regularOccurrence, Healthy, masked, Set.indicator,(hE.smooth i).symmetry k U]
  · have he : Healthy R.p.threshold (R.activities.reg i).support U ↔ Healthy R.p.threshold (R.activities.reg i).support V:= by unfold Healthy; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty,he]
    simp only [Activities.regularOccurrence, masked, Set.indicator, Set.mem_setOf_eq, he,(hE.smooth i).sites U V ha] ; rfl
  by_cases he : Healthy R.p.threshold (R.activities.reg i).support U
  · rw [Activities.regularOccurrence,masked_eq _ _ _ _ he]
    exact (hb i).2 U he [] (Nat.zero_le _) (by simp)
  rw [Activities.regularOccurrence,masked_ne _ _ _ _ he,norm_zero]; exact (hb i).1

structure Tissue (o C L q w : ℝ) : Prop where
  status : (white R).Lawful o C L 0 w
  moves a b : Nonempty (R.activities.Moves a b)
  patch : Petals R q

lemma cloth (h : R.Lawful o C L q w) : Tissue R o C L q w :=
  ⟨whiteGood R h,h.labels.moves,petalReady R h⟩

variable (h : Petals R q)

include h in
lemma thin (s : ℝ) (hs : q ≤ s) : Petals R s:= by
  obtain ⟨b,hb,hX⟩:= h.price
  exact { h with price:=⟨b,hb,fun x=>⟨(hX x).1,(hX x).2.1,(hX x).2.2.trans hs⟩⟩ }

include h in
lemma e_volume (U : Config G n) : Summable (fun i=> ‖R.activities.regularOccurrence R.p i U‖) ∧
    |R.exponent U -(white R).exponent U| ≤ Fintype.card (Site n) * q := by
  obtain ⟨b,hb,hB⟩:= h.price
  let P(x : Site n) i := if (R.activities.reg i).site=x then R.p.mass (R.activities.reg i).support (b i) else 0
  let E:= fun i=> R.activities.regularOccurrence R.p i U
  have hL (x : Site n) : SumBudget (P x) q:= hB x
  have hs: Summable (fun i=> ∑ x : Site n,P x i):= summable_sum (fun i _=> (hL i).2.1)
  have ht (i : ℕ) : ‖E i‖≤ ∑ x : Site n,P x i:= by
    simp only [P,Finset.sum_ite_eq,Finset.mem_univ,↓reduceIte]
    exact ((hb i).2 U).trans (R.p.loMass _ _ (hb i).1)
  have hA: Summable (fun i=> ‖E i‖):= .of_nonneg_of_le (fun _=> norm_nonneg _) ht hs
  refine ⟨hA,?_⟩; rw [whiteExp,show (white R).exponent U -_ - (white R).exponent U= -R.activities.additive R.p U by ring,abs_neg]
  calc
    _ ≤ ∑' i, ‖E i‖ := norm_tsum_le_tsum_norm hA
    _ ≤ ∑' i,∑ x : Site n,P x i:= hA.tsum_le_tsum ht hs
    _ = ∑ x,∑' i,P x i:= Summable.tsum_finsetSum (fun x _=> (hL x).2.1)
    _ ≤ ∑ _x:Site n,q := Finset.sum_le_sum fun x _=> (hL x).2.2
    _ = _ := by simp

lemma lightWhite {ι κ V : Type*} [Fintype ι] [Fintype κ] [Fintype V] [DecidableEq V] {θ : V→ Site n}
    (Y : ι→ Value.SourceAt G θ) (K : κ→ Value.Lifted G θ R.p.threshold) {r e l y}
    (h : Value.Light R Y K r e l y) : Value.Light (white R) Y K r e l y :=⟨h.bulk,h.forced⟩


include h in
lemma paint_env : Envelope (fun U=> Real.exp (-(R.activities.additive R.p U))) :=
  Envelope.exp ⟨Measurable.neg (Measurable.tsum h.live), Fintype.card (Site n)*q, fun U=> by
    have hx := (e_volume R h U).2
    rw [whiteExp,show (white R).exponent U -_ - (white R).exponent U = - R.activities.additive R.p U by ring] at hx; exact hx ⟩
include h in
lemma paint_gauge : GaugeInvariant (fun U=> Real.exp (-(R.activities.additive R.p U))) := by
  intro k U; simp only [Activities.additive,h.toss _ k U]

lemma whiteDensity (U : Config G n) : R.eval U = Real.exp (- R.activities.additive R.p U)*(white R).eval U := by
  rw [whiteEval,← mul_assoc, ← Real.exp_add,neg_add_cancel, Real.exp_zero,one_mul]

lemma payEnv (hp : Tissue R o C L q w) : Envelope R.eval := by
  rw [show R.eval=(fun U=>_) from funext (whiteDensity R)]
  exact Envelope.mul (paint_env R hp.patch) ((white R).envelope hp.status)

section Dust
open Glyph Value
variable {V ι κ : Type} [Fintype V] [DecidableEq V] [Fintype ι] [Fintype κ] {θ : V→Site n}
    (H : ι→ SourceAt G θ) (K : κ→ Lifted G θ R.p.threshold)
lemma whiteDust (U) : dust R H K U= (Real.exp (- R.activities.additive R.p U) : ℂ) • dust (white R) H K U:= by
  -- show only scalar switch, not discarding long supports or any K
  unfold dust
  rw [whiteExp R U, sub_eq_add_neg,Real.exp_add, mul_comm (Real.exp ((white R).exponent U)), Complex.ofReal_mul, mul_smul]; rfl

variable (hp : Tissue R o C L q w)
include hp
lemma dustMoves : GaugeInvariant (dust R H K):= by
  intro k U; rw [whiteDust _ H K,whiteDust R H K U, dust_gauge (white R) H K hp.status k U];
  rw [show Real.exp (_)=_ from paint_gauge R hp.patch k U]
lemma dustEnvelope {r e l u} (hM : ∀ i, 0 < r i) (he : 0 ≤ e)
    (hY : Value.Light R H K r e l u) (hP : Background R K) : Envelope (dust R H K):= by
  have hx := dust_env (white R) H K hM he hp.status (lightWhite R H K hY) hP
  have hE := paint_env R hp.patch
  obtain ⟨C,hC⟩:= hx.cost
  obtain ⟨D,hD⟩:= hE.cost
  refine ⟨?_, D*C,fun U=>?_⟩
  · rw [show dust R H K=fun U=>_ from funext (whiteDust R H K)]
    exact (Complex.continuous_ofReal.measurable.comp hE.meas).smul hx.meas
  rw [whiteDust,norm_smul, Complex.norm_real]
  exact mul_le_mul (hD U) (hC U) (norm_nonneg _) ((norm_nonneg _).trans (hD U))
end Dust
end YM.PhysicalNext.InteractingRank.Soft
