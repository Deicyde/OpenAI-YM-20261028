import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
/-!
 # Loft Leaf vs companion V9.Com.Mat kernel. one genuine support assignment across Y.
   Keep κ independent θ stamps until pricing performed. Domain BEFORE dropping grow,
   none displacing Y tags or sampling on physical V boundaries.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mercury
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric Set Gaussian Baffle Prism Brim Lotus Peak
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (hp : Intake P T X.x R)
  (hs : Scrim X a) (hP : Room P S T X.x)
variable {W : Config G f} {ζ d A t : ℝ} (h : Canary G d A) (hv : Drivable X d A V)
variable (M: Lotus.Leaf R)(hg:M.turn = .logKey i)
def gemE (V : Config G c)(ζ:ℝ)(u:I→G.Color) := M.ingredient (strip6 X a V u)*creates X ζ u
def gemP (V : Config G c)(ζ:ℝ)(w : Prices G I) := gemE X i R a M V ζ (peanuts X a V R.beta w)
omit [DecidableEq I] in
private def photoR : I×G.ColorIndex ↪ ↥(podium S G Y X.B) := {
  toFun j := ⟨scoop X a j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun x hx=> a.stores j.1 (halo_spec.mpr
    ⟨_,Finset.mem_singleton_self _,le_trans hx (show 25*radiusB X.x≤ Heir.reach X.x+4 by unfold Heir.reach; omega)⟩)⟩⟩
  inj' p q h := (scoop X a).injective (congr_arg Subtype.val h) }

include hg hs hP
omit [DecidableEq I] in
lemma gand (l : ℕ)(V : Config G c) (ζ:ℝ) (Ñ : ChartRatio G) (W : ℝ) (z : Air f G) (d' : F.Slice G) :
    M.floret ((vary X V).wrapY d') {Opacity.key S i} W ζ Ñ (own {Opacity.key S i}) l z= gemP X i R a M V ζ (WithLp.ofLp z ∘ scoop X a) := by
  let Q:= (vary X V).wrapY d'
  unfold Leaf.floret
  rw [hg, if_pos (show Wing.badge (.logKey i) S∈({Opacity.key S i}) from Finset.mem_singleton_self _)]
  let u:=worldZ Q R.beta z; let w:=peanuts X a V R.beta (WithLp.ofLp z ∘ scoop X a)
  have he j : u (a.address j)=w j:= shuttle X a hs hP d' R.beta z j V
  have hm:M.crest=(R.activities.reg i).support:=by unfold Leaf.crest; rw [hg]; rfl
  have hQ: Agrees (inspected M.crest) (Q.input u) (strip6 X a V w) := hm.symm ▸ entered X a hs d' u he
  have hz:= M.specific (Q.input u) (strip6 X a V w) hQ
  let H:= X.plaza (baseRead (R.activities.reg i).support X.x S)
  have hv : Q.enforce (2*ζ) u H=creates X ζ w := by
    unfold enforce creates H; rw [plaza_cal X a hs, Finset.prod_map]; refine Finset.prod_congr rfl fun j _ => ?_
    change X.χ.innerShare _ (‖u (a.address j)‖)=_; rw [he]; rfl
  change M.paidU Q ζ u* floating ..=_; unfold Leaf.paidU Leaf.fond; rw [hg, show Q.plaza (areas R T 0 Q.B (Wing.badge (.logKey i) S))=H from rfl];
  change M.ingredient (Q.input u)* _ * floating _ _ _ _ _ _ _ _ (Finset.erase ({Opacity.key S i}) (Wing.badge _ S))=_
  rw [hz,(show (Wing.badge (.logKey i) S)=Opacity.key S i from rfl),Finset.erase_singleton, show Q.enforce (2*ζ) u H=_ from hv]; unfold floating; rw [Finset.prod_empty,mul_one]; rfl
omit hs hP hg
omit [DecidableEq I] in
lemma mint_m (V:Config G c)(ζ:ℝ) : Measurable (gemP X i R a M V ζ):=by
  let k p:=peanuts X a V R.beta p
  have hk : Measurable k := measurable_pi_lambda _ fun j => measurable_const.add (Measurable.const_smul (g:=fun p:Prices G I=>tape p j) ((measurable_pi_apply j).comp tape.measurable) (gStep R.beta))
  have hx:= Art.entering X (V:=fun _ : Prices G I=>V) (Y:=fun _=> X.Y) measurable_const measurable_const ((measure_tap X a).comp hk)
  have hg : Measurable (fun p=> creates X ζ (k p)) := Finset.measurable_fun_prod _ fun j _=> (X.χ.smooth.continuous.measurable).comp
    (((((measurable_pi_apply j).comp hk).norm).div_const _).pow_const _)
  exact (M.borel.comp hx).mul hg

include hg hs hP
lemma radiance (l : ℕ) (V:Config G c)(ζ:ℝ) (Ñ : ChartRatio G) (W : ℝ) (hV : (Pond.circuit (podium S G Y X.B) (vary X V).relating).PosDef) :
    let K := Opacity.key S i; M.cinema (vary X V) {K} W ζ Ñ l (podium S G Y X.B)=∫ w,gemP X i R a M V ζ w ∂(Gaussian.cloud (Malachite.lamp6 X a V)) := by
  intro K
  unfold Leaf.cinema
  let S' := podium S G Y X.B; let B:=Pond.circuit S' (vary X V).relating; let f z:=gemP X i R a M V ζ z; let μ:=Gaussian.cloud (Malachite.lamp6 X a V); let e:=photoR X i R a; let f' (x:Poll.Body (↥S')) := WithLp.ofLp x ∘ e
  have hh : MeasurePreserving f' (Poll.sweep B) μ := registering X V i R a S' hV.posSemidef e (fun _=> rfl)
  have he (d:F.Slice G): (∫ z:Poll.Body (↥S'), Shield.lens₀ B z * M.floret ((vary X V).wrapY d) {K} W ζ Ñ (own {K}) l (Pond.spill S' z))=∫ z,f z ∂μ:=by
    let F (z:Poll.Body (↥S')):= M.floret ((vary X V).wrapY d) {K} W ζ Ñ (own {K}) l (Pond.spill S' z)
    change (∫ z,Shield.lens₀ B z*F z)=_; rw [←Shield.recommends B hV F]
    have hx z:F z=f (f' z):=by unfold F K; rw [gand X i R a hs hP M hg]; unfold f; congr 1; funext j; exact congr_arg (fun v:Poll.Body (↥S')=> v (e j)) (Pond.settled S' z)
    simp_rw [hx]
    have hx':=(mint_m X i R a M V ζ).aestronglyMeasurable (μ:=μ)
    rw [← hh.map_eq] at hx' ⊢; exact (integral_map hh.aemeasurable (show AEStronglyMeasurable f _ from hx')).symm
  change (∫ d:F.Slice G, (∫ z, Shield.lens₀ B z*M.floret ((vary X V).wrapY d) {K} W ζ Ñ (own {K}) l (Pond.spill S' z)) ∂F.order G)= _
  simp_rw [he]; simp; rfl
end YM.PhysicalNext.Repeat.Mercury
