import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Fairum
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Jac

/-! # Uniform neighborhood for sector families: pointwise Holder later.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Glass
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets Art Silica Poll Pond  Eider Flux Zest
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {x:E}
variable {j n : ℕ} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {X : Coat T F} {I : Finset (Bond f)} {η r Q q a β b p v d t W σ : ℝ} {C : E → Config G c}
variable (H : Glass P X C x j W) {Y : A→ F.Slice G} (U : A→ Air f G) {Ñ : ChartRatio G} {R : Rep G f}
variable (hq : Room P S T X.x) (hp : Canary G b p) (he : Intake P T X.x R)
include hq H hp
lemma towers (I : Finset (Bond f)) (hR : 0<β) :
    Zest (fun a i=> Flux.jacL I (X.wrapY (Y a)) b β (C i) (U a)) x j ∧
      Zest (fun a i=> Pond.swim (lensS I G) (course (X.wrapY (Y a)) b β (U a) (C i))- Pond.swim (lensS I G) (U a)) x j := by
  let Y' (a):= X.wrapY (Y a)
  let V a i:= vary (Y' a) (C i)
  have hx (a:A): V a x=Y' a := by unfold V; rw [H.lifts]; rfl
  let Q a:=worldZ (Y' a) β (U a)
  obtain ⟨hX,h⟩:= H.foreshadow (Y:=Y) Q hp
  have hs:=H.settles (Y:=Y) hq; obtain ⟨K,hK,h₂⟩:=hs.post
  have hv:Zest (fun a (_:E)=> voltage (Y' a)) x j := Zest.parallel hK fun a=> by rw [← hx a]; exact (h₂.self_of_nhds a).bound
  let A' a i k:= Eider.plume G X.χ b (G.mat (Silica.action X (C i) k)) (Q a k)
  have hh:Zest A' x j := Zest.folds fun i=> (h i).1
  refine ⟨Zest.full I _ (fun i _=> (h i).2),?_⟩
  let g := gStep β; have hg:0<g:= inv_pos.mpr (Real.sqrt_pos.mpr hR)
  let M:Directions G f →ₗ[ℝ] Body (↥(lensS I G)) := { toFun p:=Pond.swim _ (WithLp.toLp 2 (stand p)), map_add' _ _:=rfl,map_smul' _ _:=rfl }
  refine (( (hh.plusminus (hs.plusminus hv)).scalar g⁻¹).replay M.toContinuousLinearMap).congr (Eventually.of_forall fun i a=>?_)
  let Z:= (X.wrapY (Y a)).atmos (U a)
  suffices hf : steer (Y' a) b (Q a) (C i)=voltage (Y' a)+g • Z+A' a i by
    have ht : M (g⁻¹ • (steer (Y' a) b (Q a) (C i)-voltage (V a i)))=M (g⁻¹ • (A' a i - (voltage (V a i)-voltage (Y' a)))) + M Z := by
      rw [← map_add,hf]; apply congrArg (fun x=> M x)
      rw [smul_sub, smul_add,smul_add, inv_smul_smul₀ hg.ne',smul_sub,smul_sub]; abel
    change M _= _; exact (eq_sub_of_add_eq ht.symm)
  funext y; rfl

include he
lemma thorn (Z : Molecule S) (l : ℕ) (hP : LocalRatio Ñ) (ha : 0<a*X.t) (hv : 8*a*X.t ≤ b/2) (hh : 4*a*X.t < Ñ.radius) :
    Zest (fun a' i=> Polar.floating (vary (X.wrapY (Y a')) (C i)) a R W Ñ (course (X.wrapY (Y a')) b R.beta (U a') (C i))
      (own Z) l Z) x j := by
  let V a:= X.wrapY (Y a)
  let Q a:=worldZ (V a) R.beta (U a); let S k y:= steer (V k) b (fun i=> prune b (Q k i)) (C y)
  let P a i:=vary (V a) (C i); let T' t:= (V t).input (Q t)
  let K t y:= sweepZ (P t y) R.beta (S t y)
  have hx: Zest S x j := (H.foreshadow (Y:=Y) Q hp).1
  let L : Directions G f→ₗ[ℝ] Air f G := { toFun t:= WithLp.toLp _ (stand t),map_add' _ _:=rfl,map_smul' _ _:=rfl }
  have hK: Zest K x j := (((hx.plusminus (H.settles (Y:=Y) hq)).scalar (gStep R.beta)⁻¹).replay L.toContinuousLinearMap)
  refine (Zest.full Z _ (fun i _=> H.glassy T' (Y:=Y) hq S hx he (own Z) l ha hh hP i hK)).congr ?_
  obtain ⟨p,hF⟩:= H.sails
  filter_upwards [Silica.nearby X hp H.lifts hF,H.brews.1] with y hy hT t; exact
    (thatch (V t) hp _ _ W Z l Ñ (show Drivable (V t) b _ _ from ⟨hy.good⟩) ha hv hT hq he (U t)).symm
end YM.ConnectedActivityE6.Blaze.Glass
