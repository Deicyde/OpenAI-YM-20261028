import YM.AnalyticBridge.ANNULUS_RATIO_INSERTIONS.Precipitation
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Malachite.Poles
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Prism.Det

/-!
# Wages for σ comparison Books. FUND even total outside price buys.

Planning {P.Lead,...}, holds in exact config, no buying from hypothetical
 all-warm tower. Derive Holds positivity on actual sector, THEN apply through6.
 For exterior flags Vrel gives access back. Must use if W not at period interior.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Brim
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Silica Eider Metric Set Gaussian Tablet Quill  Prism
open WardBin.Lies Push.PriceCompiler Foramen Gate
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable {B : BudgetPoint} {Y : Support c} {n p j : ℕ} {v b r q η z : ℝ} {X : Coat T F} {L : Side}

section poles
lemma arbors (h : Rotator P L η r q v X) : Allow X.relating (along S) (tubularPrice G L) (retain η r q) (q⁻¹/2) (1+Window.payE η r q (tubularPrice G L)):=
    ⟨h.scale.census,Window.twin ..,h.full.prices,half_pos (inv_pos.mpr h.scale.fuel), add_pos_of_pos_of_nonneg zero_lt_one h.scale.disc,
      (increase (h.scale.mate X.shutter) le_rfl (le_add_of_nonneg_left zero_le_one)).1,h.scale.ground_C X.shutter h.cap⟩
abbrev silver (G : Gauge) (L : Side) (η r q : ℝ) := let m:=tubularPrice G L; Window.payE (retain η r q) (q⁻¹/2) (1+Window.payE η r q m) m

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {Z : E → Config G c} {x : E} {Y' : Support f} {I:Type}
variable (a : Museum F X.x (bareStores S) Y' Y I) (hr : Rotator P L η r q v X)
  (hz : Z x=X.V) (hM : Mode Z x n b) (hp : Tablet n 0 z b (fun i=> (vary X (Z i)).plate) (along S) (along S) x)

include hr hz
lemma driftPrice {b'} (hp : Tablet n 0 z b' (fun i=> (vary X (Z i)).plate) (along S) (along S) x) :
    let C := facePrice n X.B (tubularPrice G L) z (Window.payE η r q (tubularPrice G L))
    let K := fun i => (vary X (Z i)).relating
    Tablet n 0 C (driftP n b') K (along S) (along S) x ∧ ∀ᶠ i in 𝓝 x,(K i).PosDef := by
  intro C K
  have he:=padjets X.shutter hp (show Allow _ (along S) (tubularPrice G L) η r q from (by
    rw [show (vary X (Z x)).plate=X.plate by rw [hz]; rfl]; exact hr.scale)) hr.full.prices.le
  have hv : Tablet n 0 C (driftP n b') K (along S) (along S) x := by
    refine (((he.joined he.reverse).scalar (1/2:ℝ)).tilt ?_ le_rfl le_rfl le_rfl); rw [Real.norm_eq_abs,abs_of_nonneg (by norm_num)]; exact le_of_eq (by unfold C; ring)
  have ht := arbors hr; refine ⟨hv,?_⟩
  have hh : ContinuousAt K x := by apply continuousAt_pi.mpr; intro i; apply continuousAt_pi.mpr; intro j; exact (hv.singular i j).smooth.continuousAt
  have hg : FreeResolvent.Gap (K x) (q⁻¹/2) := by rw [show K x=X.relating from (by unfold K; rw [hz]; rfl)]; exact ⟨ht.ground⟩
  let Y:= q⁻¹/2/2; have hY:= half_pos ht.down
  filter_upwards [AnalyticBridge.RelativeLogdet.Differential.holds hh hg Y (half_lt_self ht.down) (FreeResolvent.native c) (along S)]
    with i hi; exact Control.definite (Window.twin ..) hi.lower hY

variable [Fintype I] [DecidableEq I]
include a in
omit [NormedSpace ℝ E] [NormedAddCommGroup E] in
lemma value6 (i j) : ‖(lamp6 X a (Z x))⁻¹ i j‖ ≤ silver G L η r q := by
  rw [hz]; let H:= (arbors hr).sub (scoop X a)
  exact only_price H.flatup.1 H.weather.1.le i j
end poles

section sale
variable (G : Gauge) (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (n : ℕ)
    (χ:Chi) (W:ℝ) (o : ConnectedActivityE6.Target.Order G W)
    {V : ℝ→ℝ} (hv : Rate G L (-(1/2)) V) (hh : ∀ᶠ x in atTop,0 ≤ V x)
include hD hv hh
lemma canopies : ∃ M K : ℝ→ℝ, Rate G L 0 M ∧ Rate G L (-(1/2)) K ∧ ∀ᶠ s in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L s S T → ShellAccess S G s W o.K o.γ →
    ∀ (F : Forest S.ratio) (X : Coat T F), X.x=s → X.χ=χ→ X.width=o.K → X.manifest → Rotator P L o.eta o.gap o.ample o.indexPay X →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Z : E → Config G c) (x:E), Z x=X.V → Mode Z x n (V s) →
      0 ≤ M s ∧ 0 ≤ K s ∧
      EdgePay (fun i=> (vary X (Z i)).relating) n (M s) 1 x ∧ (∀ i, Brush n (K s) 1 (fun j=> voltage (vary X (Z j)) i) x) ∧
        ∀ᶠ y in 𝓝 x,(vary X (Z y)).relating.PosDef := by
  obtain ⟨b,C,hb,-,hq⟩:= vines P L D hD o.K o.γ W χ n o.f hv hh 0
  obtain ⟨a,ha,hK⟩:= bounded_stencils P D hD
  let C:= carat D P L 0 a; let u x:=kernelGrowth (radiusB x) G (V x); let M x:=facePrice n (radiusB x) (tubularPrice G L) (C*C+1) (Window.payE o.eta o.gap o.ample (tubularPrice G L)); let k x:= M x*(1+driftP n (u x+u x))^n
  have hc : Rate G L 0 M:= polynomial G L n (tubularPrice G L) (C*C+1) (Window.payE o.eta o.gap o.ample (tubularPrice G L)); have hu : Rate G L 0 u:= Gate.jet_growth G L (hv.weaken (by norm_num))
  have hF : Rate G L 0 k:= by simpa only [zero_mul,add_zero] using! hc.mul (((Rate.const 1).add ((hu.add hu).mul_left (n:ℝ))).pow n)
  refine ⟨k,fun x=>|b x|,hF,hb.compare (Eventually.of_forall fun x=>by rw [abs_abs]),?_⟩
  filter_upwards [hq] with s hx c f S T hS hs hj F X hX hχ hB he hr E _ _ Z x hZ hM; subst s
  have hz := Gate.plates X D hS hs.length_eq hr.room hM a ha (hK c f S T hS hs.funds) (show 0 ≤ (0:ℝ) from le_rfl) P.top.width_pos
  have heZ:Tablet n 0 (C*C+1) (u X.x+u X.x) (fun i=> (vary X (Z i)).plate) (along S) (along S) x:= hz
  have hp:= driftPrice (z:=C*C+1) hr hZ heZ; have he' : vary X (Z x)=X:= by rw [hZ]; rfl
  have hp₁: Tablet n 0 (M X.x) (driftP n (u X.x+u X.x)) (fun i=> (vary X (Z i)).relating) (along S) (along S) x:=hp.1
  refine ⟨mul_nonneg hp₁.basis (pow_nonneg (add_nonneg zero_le_one hp₁.pos) _),abs_nonneg _,fun i j=> (hp₁.singular i j).trim,
    ?_,hp.2⟩
  have ht:(vary X (Z x)).manifest:= Eq.mp (by rw [he'] : X.manifest = (vary X (Z x)).manifest) he
  have hq:Allow (vary X (Z x)).plate (along S) (tubularPrice G L) o.eta o.gap o.ample := by rw [he']; exact hr.scale
  exact (hx c f S T hS hs hj F X E Z x rfl hB hχ hM ht hq).1
end sale
end YM.PhysicalNext.Repeat.Brim
