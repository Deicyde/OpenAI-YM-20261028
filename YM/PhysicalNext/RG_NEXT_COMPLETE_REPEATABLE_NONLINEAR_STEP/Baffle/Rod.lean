import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Facility
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Levan
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Opacity
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Zest
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Patch
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Cover

/-!
# Germ input arms in common coordinates. Exact equality here on E6 wedge

With marginal of real E6 dice, pushed by `Coordinates`, NOT `spectacle`.
Use wherever positive on the followed arc. No folklore Frame agreement.
Two compact coordinate masses with visible normalizers are compared later.
An exact equality of any two MEASURES via ad hoc witnessing over all test
vectors is not needed; rather equality with this marginal **of E6** and
separate the companion difference. No undeclared output flags omitted.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell  Poll Pond Polar
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} (V : Config G c)
variable {w d t b W v : ℝ}
section Rod
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (ζ : ℝ)
  (hp : Intake P T X.x R)
  (hs : Scrim X a) (hP : Room P S T X.x)

-- universal aura uses no Y and no κ outside; not true for cuts on wrong active.
def creates (ζ : ℝ) (w : I→G.Color) := ∏ i : I, X.χ.innerShare (2*ζ*X.t) ‖w i‖
abbrev award (R : Rep G f) (i : ℕ) := R.activities.regularOccurrence R.p i
def costE (u : I→G.Color) := Real.exp (-award R i (strip6 X a V u)*creates X ζ u)-1
def payE (w : Prices G I) := costE X V i R a ζ (peanuts X a V R.beta w)

include hp hs hP
omit [DecidableEq I] in
lemma it_agrees (l : ℕ) (Ñ : ChartRatio G) (W : ℝ) (z : Air f G) (d : F.Slice G) :
    floating ((vary X V).wrapY d) ζ R W Ñ z ∅ l {Opacity.key S i}= payE X V i R a ζ (WithLp.ofLp z ∘ scoop X a) := by
  let Q:= (vary X V).wrapY d
  unfold floating; rw [Finset.prod_singleton]
  let u:=worldZ Q R.beta z; let w:=peanuts X a V R.beta (WithLp.ofLp z ∘ scoop X a)
  have he j : u (a.address j)=w j:= shuttle X a hs hP d R.beta z j V
  have hz := valueE R i (hp.cap.labels.regular.smooth i) (Q.input u) (strip6 X a V w) (entered X a hs d u he)
  let H := X.plaza (baseRead (R.activities.reg i).support X.x S)
  have hv : Q.enforce (2*ζ) u H=creates X ζ w := by
    unfold enforce creates H; rw [plaza_cal X a hs, Finset.prod_map]; refine Finset.prod_congr rfl fun j _ => ?_
    change X.χ.innerShare _ (‖u (a.address j)‖)=_; rw [he]; rfl
  change Real.exp (-R.activities.regularOccurrence R.p i _ * Q.enforce (2*ζ) u H)-1=costE X V i R a ζ w
  change Real.exp (-R.activities.regularOccurrence R.p i (Q.input u) * _) -1=_
  rw [hz,hv]; rfl

omit hs hP [DecidableEq I] in
lemma payE_m : Measurable (payE X V i R a ζ) := by
  let k p:=peanuts X a V R.beta p
  have hk : Measurable k := measurable_pi_lambda _ fun j => measurable_const.add (Measurable.const_smul (g:=fun p:Prices G I=>tape p j) ((measurable_pi_apply j).comp tape.measurable) (gStep R.beta))
  have hf : Measurable (award R i):= masked_measurable _ _ _ ((hp.cap.labels.regular.smooth i).borel)
  have hx:= Art.entering X (V:=fun _ : Prices G I=>V) (Y:=fun _=> X.Y) measurable_const measurable_const ((measure_tap X a).comp hk)
  have hg : Measurable (fun p=> creates X ζ (k p)) := Finset.measurable_fun_prod _ fun j _=> (X.χ.smooth.continuous.measurable).comp
    (((((measurable_pi_apply j).comp hk).norm).div_const _).pow_const _)
  exact (((Measurable.mul (((hf.comp hx).neg)) hg).exp).sub_const 1)

omit [DecidableEq I] hp hs hP in
private def berth : I×G.ColorIndex ↪ ↥(podium S G Y X.B) := {
  toFun j := ⟨scoop X a j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun x hx=> a.stores j.1 (halo_spec.mpr
    ⟨_,Finset.mem_singleton_self _,le_trans hx (show 25*radiusB X.x≤ Heir.reach X.x+4 by unfold Heir.reach; omega)⟩)⟩⟩
  inj' p q h := (scoop X a).injective (congr_arg Subtype.val h) }

-- coordinate mapping between exact normalized measures. Valid all hypotheses X,
-- never require probability-preservation on V9 replaced. No assumption λ Lebesgue scale.
omit hp hP hs in
lemma registering (M : Finset (Tubular f G)) (h : (Pond.circuit M (vary X V).relating).PosSemidef) (e : I×G.ColorIndex ↪ M) (he : ∀ j, (e j).val=scoop X a j) :
    MeasurePreserving (fun z : Poll.Body (↥M) => (WithLp.ofLp z ∘ e)) (Poll.sweep (Pond.circuit M (vary X V).relating)) (Gaussian.cloud (Malachite.lamp6 X a V)) := by
  have hr : (Pond.circuit M (vary X V).relating).submatrix e e=Malachite.lamp6 X a V := by
    ext i j; change (vary X V).relating (e i).val (e j).val=_; rw [he,he]; rfl
  rw [← hr]; exact (margin_law _ h).comp (Gaussian.preserving_cloud _)

lemma arcBar (l : ℕ) (Ñ : ChartRatio G) (W : ℝ) (hV : (Pond.circuit (podium S G Y X.B) (vary X V).relating).PosDef) :
    let K := Opacity.key S i; Shield.bars (podium S G Y X.B) (vary X V) {K} R Ñ W ζ l=∫ w,payE X V i R a ζ w ∂(Gaussian.cloud (Malachite.lamp6 X a V)) := by
  intro K
  unfold Shield.bars; let M:=podium S G Y X.B
  let B:=Pond.circuit M (vary X V).relating; let f z:= payE X V i R a ζ z; let μ:= Gaussian.cloud (Malachite.lamp6 X a V); let b:=berth X i R a; let f' (x:Poll.Body (↥M)) := WithLp.ofLp x ∘ b
  have hh : MeasurePreserving f' (Poll.sweep B) μ := registering X V i R a M hV.posSemidef b (fun _=> rfl)
  have he (d : F.Slice G) : (∫ z : Poll.Body (↥M), Shield.lens₀ B z * floating ((vary X V).wrapY d) ζ R W Ñ (Pond.spill M z) (own {K}) l {K})=∫ z,f z ∂μ := by
    let F (z:Poll.Body (↥M)):=floating ((vary X V).wrapY d) ζ R W Ñ (Pond.spill M z) (own {K}) l {K}
    change (∫ z,Shield.lens₀ B z * F z)=_; rw [← Shield.recommends B hV F]
    have hx z : F z=f (f' z) := by
      unfold F; rw [show own ({K} : Molecule S)=∅ from ?_,it_agrees X V i R a ζ hp hs hP l Ñ W]; unfold f; congr 1; funext j
      · exact congr_arg (fun v:Poll.Body (↥M)=> v (b j)) (Pond.settled M z)
      ext i; simp [K,Opacity.key,own]
    simp_rw [hx]
    have hx' := (payE_m X V i R a ζ hp).aestronglyMeasurable (μ:=μ)
    rw [← hh.map_eq] at hx' ⊢; exact (integral_map hh.aemeasurable (show AEStronglyMeasurable f _ from hx')).symm
  change (∫ d : F.Slice G, (∫ z, Shield.lens₀ B z * floating ((vary X V).wrapY d) ζ R W Ñ (Pond.spill M z) (own {K}) l {K}) ∂ F.order G) = _
  simp_rw [he]; simp; rfl
end Rod
end YM.PhysicalNext.Repeat.Baffle
