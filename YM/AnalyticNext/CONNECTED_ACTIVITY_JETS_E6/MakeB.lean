import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Issue

/-!
# Measurability of untouched expressions on per-orientation data

No convergence issue hidden--true at allotted periods. Hard indicator
points not discarded. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Coat
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f n : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {A W γ x : ℝ} {η r Q Y : ℝ} {L : Side} (X : Coat T F)

lemma site_b (i : Site c) (k : S.Choices) : Measurable (fun U : Config G f=> Tags.siteMass U k i) :=
  measurable_const.mul <| (S.patch.frameMass_meas _).comp (show Continuous _ by unfold expandAt; fun_prop).measurable
lemma pin_b (i : Bond c) (k : S.Choices) (h : P.Funds S T) : Measurable (fun U : Config G f => Tags.pinMass U k i) :=
  measurable_const.mul <| (S.patch.predictorMass_meas _).comp (S.connector_meas (funds_branch h) _ i)
lemma fine_b (i : Cell f) (A : Stores S) : Measurable (fun U : Config G f => Mask.fine A X.χ i X.t U) := by
  unfold Mask.fine
  have he : Measurable (fun U : Config G f => X.χ.innerShare (X.t/4) (toll U i)) :=
    X.χ.smooth.continuous.measurable.comp (((toll_meas i measurable_id).div_const _).pow_const 2)
  split_ifs
  · exact measurable_const.sub he
  exact he

lemma bond_b (i : Bond c) (A : Stores S) (h : P.Funds S T) : Measurable (fun U=>Mask.noise A X.χ i X.t W U X.k X.V) := by
  unfold Mask.noise
  have he := wire_meas X.k i (funds_branch h) (U:=id) measurable_id (V:=fun _=>X.V) measurable_const
  have hx := X.χ.smooth.continuous.measurable.comp ((he.div_const (W*X.t)).pow_const 2)
  split_ifs
  · exact measurable_const.sub hx
  exact hx
lemma contract_b (i : Site f) (l : Finset ℕ) (R : Rep G f) : Measurable (fun U => Contract.charges R l U i) := by
  unfold Contract.charges; apply Measurable.ite _ measurable_const measurable_const
  by_cases hp : i ∈ Contract.covered R l
  · simp [hp]
  simp only [hp,not_false_eq_true,true_and]
  exact (RG.flags_open (G:=G) i R.p.threshold).measurableSet
lemma cone_b (i : Bond f) (a : ℝ) : Measurable (fun u => X.cone a u i) := X.χ.smooth.continuous.measurable.comp
  (show Continuous (fun u : Directions G f => (‖u i‖/(a*X.t))^2) by fun_prop).measurable
lemma enforce_b (a : ℝ) (A : Finset (Bond f)) : Measurable (fun u => X.enforce a u A) :=
  Finset.measurable_fun_prod _ fun _ _ => X.cone_b _ _
lemma gentry_b (i : Bond f) (Ñ : ChartRatio G) (h : LocalRatio Ñ) (a : ℝ) : Measurable (fun u => X.gentry Ñ a u i) :=
  (X.cone_b i _).mul (Real.measurable_log.comp (h.borel.comp (measurable_pi_apply i)))

lemma origin_b (hp : P.Funds S T) (V : Config G c) (k : S.Choices) (i : Spot c f) (x : ℝ) :
    Measurable (fun U=> principal T x U V (S.prediction U k) i) ∧ Measurable (fun U => yielding T x U V k i) := by
  obtain ⟨u,b,h,-⟩ := hp.feeds
  rw [← hp.high] at h
  have hx (i : Twin f) : Continuous (fun U => T.Xf (till x) U i) := SectorMeasure.plotted_cont h ..
  have hn := S.prediction_meas (funds_branch hp) k
  rcases i with i|i|i|i
  · let R := till x; let t:=Pressure.fiery G x S.patch.L; let s := Pressure.temp x
    have hP : Continuous (fun U => ∑ j : Bool,(‖T.Mv R s V (i,j)‖^2/2 - inner ℝ (T.Mv R s V (i,j)) (T.Xf R U (i,j)))) := by
      unfold R; fun_prop
    refine ⟨(env_crown h R 1 t i).meas.add hP.measurable, (show Continuous (fun U=>soft T x U V k i) from ?_).measurable⟩
    unfold soft SliceRows.bill entryCost; simp only [Sum.elim]; unfold flaw faceValue; fun_prop
  · have hh : Measurable (fun U => T.workI (till x) (S.prediction U k) V (Pressure.temp x) i) :=
      (show Continuous (fun U => T.workI (till x) U V (Pressure.temp x) i) by unfold Tube.workI monetary wire Z; fun_prop).measurable.comp hn
    exact ⟨hh,hh⟩
  · let t:=Pressure.temp x; let R := till x
    have hQ : Continuous (fun p : Config G f×Config G c => T.workL R p.1 p.2 V t i) := by
      unfold Tube.workL unzip Z; unfold R; fun_prop
    have hh : Measurable (fun U => T.workC R V t i+(T.workL R U (S.prediction U k) V t i+T.workD R V t i)) :=
      measurable_const.add ((hQ.measurable.comp (measurable_id.prodMk hn)).add measurable_const)
    exact ⟨hh,hh⟩
  exact ⟨measurable_const,measurable_const⟩

open Raw
lemma rawlog_b {R : Rep G f} (h : Intake P T x R) (V : Config G c) (i : LogLetter c f) :
    Measurable (fun U => expo T x R U V i) := by
  have ht {d} (B : ℕ → Atom G d) (v : ℝ) (i : Trans f) : Measurable (fun U=>translateValue R.p B v U i) :=
    measurable_const.mul (((masked_measurable _ _ _ ((B i.2.2).unmasked_cont (n:=f) i.2.1).measurable)).comp
      (continuous_pull i.1 (0:Site f)).measurable)
  have hh (K : PathData G) (p : Clip) (x : Cell f) (s : ℕ) (u : ℝ) (i : ℕ×ℕ) :
      Measurable (fun U=>pairTail K p s 1 u x U i) := by
    unfold pairTail
    by_cases he : long K s 1 x.2 i
    · simp only [he,true_and]
      refine Measurable.ite (PathData.kept_closed ..).measurableSet (show Continuous _ from ?_).measurable measurable_const
      unfold PathData.ellTerms Slot.atSite expandAt; fun_prop
    simp only [he,false_and,↓reduceIte]; exact measurable_const
  rcases i with i|i|i|i|i|i
  · exact (masked_measurable _ _ _ ((h.cap.labels.regular.smooth i).borel)).neg
  · exact ht _ _ _
  · exact ht _ _ _
  · exact ht _ _ _
  · refine measurable_const.mul ((hh _ _ (i.2.2.1,i.2.1) _ _ i.2.2.2).comp
      (continuous_pull (G:=G) i.1 (0:Site f)).measurable)
  exact measurable_const
end YM.ConnectedActivityE6.Coat
