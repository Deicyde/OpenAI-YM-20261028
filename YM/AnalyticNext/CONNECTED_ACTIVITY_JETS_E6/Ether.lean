import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Paisley
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Ryme

/-!
# Compact chart animation and all readouts at held U

 Use saturation with a constant (m can be chosen independent of Y/U and
 occupation bits). With this hypothesis approvals, gates even if read at
 unhealthy U constants; do not differentiate ticket cost in U.
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
variable (H : Glass P X C x j W) {Y : A→ F.Slice G} (U : A→ Config G f)
variable {u : A→ E → Directions G f} {w : A→ E → Air f G} {k : Finset ℕ} (h : Room P S T X.x)
include H
lemma gels_norm {ι : Type} (Y : ι→ G.Color) (h : ∀ i,‖Y i‖≤ 3*d) (p' : Canary G d p) (i : Bond f) :
    Zest (fun b t=> Eider.plume G X.χ d (G.mat (Silica.action X (C t) i)) (Y b)) x j ∧
      Zest (fun b t=> Eider.palm G X.χ d (G.mat (Silica.action X (C t) i)) (Y b)) x j := by
  have hd:= p'.warm
  obtain ⟨m,hm⟩:=H.sails
  have he := chargeMode X _ hm i
  let S:= Metric.closedBall (1:G.Mat) p; let T:= Metric.closedBall (0:G.Color) (3*d)
  have hp := (isCompact_closedBall (1:G.Mat) p).prod (isCompact_closedBall (0:G.Color) (3*d))
  let f b t:= (G.mat (action X (C t) i),Y b)
  have hf : Zest f x j := Zest.pair (Zest.single he.smooth) (Zest.parallel (by positivity) h)
  have hg : ∀ᶠ t in 𝓝 x, ∀ b,f b t∈S ×ˢ T := by
    filter_upwards [nearby X p' H.lifts hm] with t ht b; exact
      ⟨by exact Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact (ht.good i).1.le),Metric.mem_closedBall.mpr ((dist_zero_right ..).trans_le (h _))⟩
  exact ⟨hf.emigrate (p:=uncurry (Eider.plume G X.χ d)) hp (fun ⟨x,y⟩ hi=> (Eider.sheen p' X.χ y x (by simpa [Metric.mem_closedBall,dist_eq_norm] using! hi.1)).of_le
    (WithTop.coe_le_coe.mpr le_top)) hg,hf.emigrate (p:=uncurry (palm G X.χ d)) hp (fun ⟨x,y⟩ hi=> Eider.lift p' X.χ x y (by
    simpa [Metric.mem_closedBall,dist_eq_norm] using! hi.1)) hg⟩

lemma foreshadow (B:A→ Directions G f) (p' : Canary G d p) :
    let V t i:= prune d (B t i)
    Zest (fun t y=> steer (X.wrapY (Y t)) d (V t) (C y)) x j ∧
      ∀ i:Bond f,Zest (fun t y=> Eider.plume G X.χ d (G.mat (Silica.action X (C y) i)) (B t i)) x j ∧
        Zest (fun t y=> steerJ (X.wrapY (Y t)) d (B t) (C y) i) x j := by
  intro V; have he i t : ‖V t i‖ ≤ 3*d := berries (B t i) p'.warm
  have hh i := H.gels_norm (fun t=>V t i) (he i) p' i
  refine ⟨Zest.folds ?_,fun i=> ⟨(hh i).1.congr ?_,(hh i).2.congr ?_⟩⟩
  · exact fun i=> (Zest.parallel (by have h:=p'.warm; positivity) (he i)).together (hh i).1
  · exact Eventually.of_forall fun t s=> (braided X p' (B s i) _).1.symm
  exact Eventually.of_forall fun t s=> (braided X p' (B s i) _).2.symm
-- masks χ algebra squared, even Z companions.
omit H in
lemma tip (a : ℝ) : ContDiff ℝ (↑j : WithTop ℕ∞) (fun p:G.Color=> X.χ.innerShare a ‖p‖) := by
  unfold Chi.innerShare; simp_rw [div_pow]; exact (X.χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp ((contDiff_norm_sq ℝ).div_const _)
omit H in
lemma elevator {Ñ : ChartRatio G} (p : LocalRatio Ñ) (he : 0 < a*X.t) (hX : 4*a*X.t < Ñ.radius) :
    ContDiff ℝ (↑j : WithTop ℕ∞) (fun y:G.Color=> X.χ.innerShare (2*a*X.t) ‖y‖ * Real.log (Ñ.J y)) := by
  refine contDiff_iff_contDiffAt.mpr fun i=> ?_
  have hI : 4*a*X.t=2*(2*a*X.t) := by ring
  have hz : 0<2*a*X.t := by rw [mul_assoc]; positivity
  by_cases ht : i∈ Metric.ball (0:G.Color) Ñ.radius
  · exact (tip (X:=X) _).contDiffAt.mul (((p.germ i ht).log (p.pos i ht).ne').of_le le_top)
  refine contDiffAt_const (c:=(0:ℝ))|>.congr_of_eventuallyEq ?_
  have hv : 4*a*X.t < ‖i‖ := hX.trans_le (by simpa [Metric.mem_ball,not_lt] using ht)
  filter_upwards [continuous_norm.continuousAt (lt_mem_nhds hv)] with y hy; have hg : X.χ.innerShare (2*a*X.t) ‖y‖=0 := by
    by_contra hm; have he:= X.χ.chosen_lt _ _ hz hm; rw [← hI] at he; exact lt_asymm he hy
  change X.χ.innerShare _ ‖y‖*_=0; rw [hg,zero_mul]

omit H in lemma fineLine (Z : Stores S) (i : Cell f) : Zest (fun a (_:E)=>Mask.fine Z X.χ i X.t (U a)) x j := by
  refine Zest.parallel zero_le_one fun i=>?_ ; rw [Real.norm_of_nonneg (Mask.fine_range ..).1]; exact (Mask.fine_range ..).2

attribute [local instance] Gauge.frobInner
lemma noiseLine (Z : Stores S) (i : Bond c) : Zest (fun a t=> Mask.noise Z X.χ i X.t W (U a) X.k (C t)) x j := by
  obtain ⟨K,hK⟩:=H.sails
  let T (a:A):= S.prediction (U a) X.k i
  have hx : Zest (fun a t=>G.mat (C t i *(T a)⁻¹)) x j := by
    -- fixed right; can use mode shift
    refine ⟨royalty G * (1+(K+1))^j, by have :=royalty_ge G; have :=hK.pos; positivity,?_⟩
    filter_upwards [widen_mode hK (show K<K+1 by linarith)] with t ht a
    simpa only [one_mul] using! (offsetB (ht.atLink i) 1 ((T a)⁻¹)).trim
  let f (a:G.Mat) := X.χ.read ((‖a-1‖/G.colorScale/(W*X.t))^2)
  have hh : ContDiff ℝ (↑j : WithTop ℕ∞) f := by
    unfold f; simp_rw [div_pow]; exact (X.χ.smooth.of_le (WithTop.coe_le_coe.mpr le_top)).comp
      ((((contDiff_norm_sq ℝ).comp (f:=fun x:G.Mat=>x-1) (contDiff_id.sub contDiff_const)).div_const _).div_const _)
  unfold Mask.noise; split_ifs
  next hi=> exact (Zest.still (1:ℝ)).plusminus (hx.wand hh)
  exact hx.wand hh
end YM.ConnectedActivityE6.Blaze.Glass
