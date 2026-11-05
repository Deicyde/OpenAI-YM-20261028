import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mercury.Oasis
/-!
 # Both arm expressions explicit... identity on stencil after FULL permits.Then price.
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
  (hp : Intake P T X.x R) (hs : Scrim X a) (hP : Room P S T X.x)
variable {W : Config G f} {ζ d A t : ℝ} (h : Canary G d A) (hv : Drivable X d A V)
variable (M: Lotus.Leaf R)(hg:M.turn= .logKey i)
variable (L : Config G f→ℝ)(hL: R.p.Regular (R.activities.reg i).support L)(hm:M.ingredient= masked R.p.threshold (R.activities.reg i).support L)
def golf (z: Prices G I):=M.ingredient (strip6 X a X.V (anchor X a z R.beta))
def box6 (d ζ : ℝ)(V: Config G c)(z:Prices G I):=tax6 X i R a d R.beta V z * (coin X i R a d R.beta ζ V z * golf X i R a M z)
def box9 (d : ℝ)(V:Config G c)(z:Prices G I):= tax9 X i R a q b d R.beta V z*(veil X a q κ b D R.p d R.beta z V * golf X i R a M z)

variable (hr: 0 < ζ*X.t) (hk:8*ζ*X.t ≤ d/2)

include h hv hs hr hk hp
include hg
lemma greater (z : Prices G I): tax6 X i R a d R.beta V z * gemP X i R a M V ζ (fast X V a d R.beta z+0)= box6 X i R a M d ζ V z:=by
   unfold box6; apply congr_arg (tax6 X i R a d R.beta V z * ·); rw [add_zero]; unfold gemP gemE; rw [show peanuts X a V R.beta (fast X V a d R.beta z)=fawn X V a z d R.beta from to_strip X V a hp.positive z d,mul_comm]; unfold coin
   by_cases he:creates X ζ (fawn X V a z d R.beta)≠0
   · unfold golf; apply congr_arg; refine M.specific _ _ ?_; rw [show M.crest=(R.activities.reg i).support from (by unfold Leaf.crest; rw [hg]; rfl)]; exact felt X V a h hv hs z hr hk he
   rw [not_not] at he; rw [he,zero_mul,zero_mul]
omit hg
include hL hm
lemma hatch (s:Prices G I)(hz: veil X a q κ b D R.p d R.beta s V≠0 → coin X i R a d R.beta ζ V s=1 ∧ Healthy R.p.threshold (R.activities.reg i).support (strip6 X a X.V (anchor X a s R.beta))):
    let f z:= magic D R.p R.beta κ z*L (a.received X.k T q b (gStep R.beta) V 1 z)
    tax9 X i R a q b d R.beta V s * f (reading9 X V a s q b d R.beta)=box9 X i R a q κ b D M d V s:=by
    intro f; unfold box9; apply congr_arg (tax9 X i R a q b d R.beta V s * ·)
    let w:=reading9 X V a s q b d R.beta; let U:=a.received X.k T q b (gStep R.beta) V 1 w; let Y:=veil X a q κ b D R.p d R.beta s V
    change Y*L U=Y*golf X i R a M s; by_cases ht:Y≠0
    swap; · rw [not_not] at ht; rw [ht,zero_mul,zero_mul]
    obtain ⟨hc,hh⟩:=hz ht
    apply congr_arg; unfold golf; rw [hm,masked_eq _ _ _ _ hh]; apply hL.sites U; apply agrees_mono _ (show (R.activities.reg i).support⊆ inspected (R.activities.reg i).support from Finset.subset_union_left)
    have he:= felt X V a h hv hs s hr hk (show creates X ζ (fawn X V a s d R.beta) ≠0 from ne_of_eq_of_ne hc one_ne_zero)
    rw [← to_strip X V a hp.positive s] at he; intro e hi hj; exact (hears9 X V a hp.positive hs s q b d e hi hj).trans (he e hi hj)
omit hL hm in
include hP hg in
lemma pop6 (l:ℕ)(Ñ:ChartRatio G)(W:ℝ) (h₀ : (lamp6 X a X.V).PosDef) (hV : (vary X V).relating.PosDef) :
    let K:=Opacity.key S i; M.cinema (vary X V) {K} W ζ Ñ l (podium S G Y X.B)=∫ w,box6 X i R a M d ζ V w ∂Gaussian.cloud (lamp6 X a X.V):=by
  intro K; rw [show M.cinema (vary X V) {K} W ζ Ñ l (podium S G Y X.B)=_ from radiance X i R a hs hP M hg l V ζ Ñ W (hV.submatrix Subtype.val_injective),reels X V a h hp.positive hv h₀ _ (hV.submatrix (scoop X a).injective) 0]
  exact integral_congr_ae (ae_of_all _ fun s=>greater X i R a hp hs h hv M hg hr hk s)
lemma pop9 (h₀ : (lamp6 X a X.V).PosDef) (hV : (lamp9 X a V).PosDef) (hh : ∀ s, veil X a q κ b D R.p d R.beta s V≠0 →
    creates X ζ (fawn X V a s d R.beta)=1 ∧ Healthy R.p.threshold (R.activities.reg i).support (strip6 X a X.V (anchor X a s R.beta))) :
    a.hymn T (gStep R.beta) q b X.k L (magic D R.p R.beta κ) 1 V= ∫ z, box9 X i R a q κ b D M d V z ∂Gaussian.cloud (lamp6 X a X.V):=by
   unfold Museum.hymn; rw [if_pos hV]; rw [reels X V a h hp.positive hv h₀ _ hV (distance9 X V a q b R.beta)]; exact integral_congr_ae (ae_of_all _ fun s=> hatch X i R a q κ b D hp hs h hv M L hL hm hr hk s (hh s))
end YM.PhysicalNext.Repeat.Mercury
