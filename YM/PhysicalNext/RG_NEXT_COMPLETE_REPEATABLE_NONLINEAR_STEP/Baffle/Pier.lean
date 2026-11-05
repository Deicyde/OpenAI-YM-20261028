import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Baffle.Cases

/-!
# Algebraic comparison after arm moves (integral sum in AFTER Meristem)

Inherits E via κ·mask from EXACT centre. V9 and E6 measures separately
transferred, exact identities. Buildings as functions of all Config fields
(equality imposed on genuine neighborhoods in specs). Signed familiar.
Licence of all P stays. At materia we need this with Paper prices of both
(before appropriating same curvature), even on Supports r around p*, even
flagged outside. Keep quantum variables all visits, no unobserved handoff.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Baffle
open Filter Function Lattice MeasureTheory Matrix Tree RG Wilson Pressure Pressure.Stores Pressure.Tube Push.SectorMeasure Push.AbsoluteSums Exterior
open Next.Fluctuations Next.SectorChange Next.SectorChange.Rows AnalyticBridge.LocalGaussian AnalyticBridge.LocalGaussianLaws
open JointLoad JointLoad.Heir AnalyticBridge.SectorAffine ConnectedActivityE6 ConnectedActivityE6.Coat ConnectedActivityE6.SliceRows
open ConnectedActivityE6.Mask ConnectedActivityE6.Blaze ConnectedActivityE6.Blaze.Brush Precision Window Control
open Push.SectorMeasure.Oriented Scroll Vine Census Progress.StationaryScenes Progress.StationaryScenes.Green Hues Rotation
open Malachite Matter Shell Flux Poll Pond Polar Silica Eider Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {T : Tube G S}
variable (X : Coat T F) {I : Type} {Y : Support c} {V : Config G c}
variable (i : ℕ) (R : Rep G f) [Fintype I] [DecidableEq I]
  (a : Museum F X.x (bareStores S) (R.activities.reg i).support Y I) (q κ : Chi) (b : ℝ) (D : Record)
  (hp : Intake P T X.x R)
  (hs : Scrim X a) (hP : Room P S T X.x)
variable {W : Config G f} {ζ d A t : ℝ} (h : Canary G d A) (hv : Drivable X d A V)
section pier

abbrev tax6 (d β : ℝ) (V : Config G c) := reads_map X V a (lamp6 X a V) d β 0
abbrev tax9 (d β : ℝ) (V : Config G c) := reads_map X V a (lamp9 X a V) d β (distance9 X V a q b β)
def coin (d β ζ : ℝ) (V : Config G c) (s : Prices G I) := creates X ζ (fawn X V a s d β)
def owe (s : Prices G I) := award R i (strip6 X a X.V (anchor X a s R.beta))

def strand6 (d ζ : ℝ) (V : Config G c) (s : Prices G I) := tax6 X i R a d R.beta V s * (Real.exp (-owe X i R a s*coin X i R a d R.beta ζ V s)-1)
def strand9 (d : ℝ) (V : Config G c) (s : Prices G I) := tax9 X i R a q b d R.beta V s * (veil X a q κ b D R.p d R.beta s V * owe X i R a s)

def sliver (V : Config G c) (z : Prices G I) := magic D R.p R.beta κ z * R.activities.E i (a.received X.k T q b (gStep R.beta) V 1 z)

variable (hr : 0< ζ*X.t) (hk : 8*ζ*X.t ≤ d/2)
include h hv hs hr hk hp
lemma crystal (s : Prices G I) : tax6 X i R a d R.beta V s * payE X V i R a ζ (fast X V a d R.beta s+0)= strand6 X i R a d ζ V s := by
  apply congr_arg (tax6 X i R a d R.beta V s * ·); rw [add_zero]; unfold payE costE coin
  rw [show peanuts X a V R.beta (fast X V a d R.beta s)=fawn X V a s d R.beta from to_strip X V a hp.positive s d]
  by_cases he : creates X ζ (fawn X V a s d R.beta)≠0
  · rw [show award R i (strip6 X a V (fawn X V a s d R.beta)) = owe X i R a s from valueE R i (hp.cap.labels.regular.smooth i) _ _ (felt X V a h hv hs s hr hk he)]
  simp only [not_not] at he; rw [he,mul_zero,mul_zero]

include hs
lemma pearl (s : Prices G I) (hz : veil X a q κ b D R.p d R.beta s V≠0 → coin X i R a d R.beta ζ V s=1 ∧ Healthy R.p.threshold (R.activities.reg i).support (strip6 X a X.V (anchor X a s R.beta))) :
    tax9 X i R a q b d R.beta V s * sliver X i R a q κ b D V (reading9 X V a s q b d R.beta)= strand9 X i R a q κ b D d V s := by
  apply congr_arg (tax9 X i R a q b d R.beta V s * ·)
  let w:= reading9 X V a s q b d R.beta; let U := a.received X.k T q b (gStep R.beta) V 1 w; let Y:= veil X a q κ b D R.p d R.beta s V
  change Y * R.activities.E i U = Y * owe X i R a s; by_cases ht : Y≠0
  swap; · rw [not_not] at ht; rw [ht,zero_mul,zero_mul]
  obtain ⟨hc,hh⟩:= hz ht
  apply congr_arg; unfold owe award Activities.regularOccurrence; rw [masked_eq _ _ _ _ hh]; apply (hp.cap.labels.regular.smooth i).sites U
  apply agrees_mono _ (show (R.activities.reg i).support ⊆ inspected (R.activities.reg i).support from Finset.subset_union_left)
  have he := felt X V a h hv hs s hr hk (show creates X ζ (fawn X V a s d R.beta)≠0 from ne_of_eq_of_ne hc one_ne_zero)
  rw [← to_strip X V a hp.positive s] at he
  intro e hi hj; exact (hears9 X V a hp.positive hs s q b d e hi hj).trans (he e hi hj)

include hP
lemma loft6 (l : ℕ) (Ñ : ChartRatio G) (W : ℝ) (h₀ : (lamp6 X a X.V).PosDef) (hV : (vary X V).relating.PosDef) :
    Shield.bars (podium S G Y X.B) (vary X V) {Opacity.key S i} R Ñ W ζ l=∫ z, strand6 X i R a d ζ V z ∂Gaussian.cloud (lamp6 X a X.V) := by
  rw [arcBar X V i R a ζ hp hs hP l Ñ W (show (Pond.circuit _ _).PosDef from hV.submatrix Subtype.val_injective),reels X V a h hp.positive hv h₀ _ (hV.submatrix (scoop X a).injective) 0]; exact integral_congr_ae (ae_of_all _ fun s=> crystal X i R a hp hs h hv hr hk s)

omit hP
lemma loft9 (h₀ : (lamp6 X a X.V).PosDef) (hV : (lamp9 X a V).PosDef) (hh : ∀ s, veil X a q κ b D R.p d R.beta s V≠0 →
    creates X ζ (fawn X V a s d R.beta)=1 ∧ Healthy R.p.threshold (R.activities.reg i).support (strip6 X a X.V (anchor X a s R.beta))) :
    a.hymn T (gStep R.beta) q b X.k (R.activities.E i) (magic D R.p R.beta κ) 1 V=∫ z, strand9 X i R a q κ b D d V z ∂Gaussian.cloud (lamp6 X a X.V) := by
  unfold Museum.hymn; rw [if_pos hV]; rw [reels X V a h hp.positive hv h₀ _ hV (distance9 X V a q b R.beta)]
  exact integral_congr_ae (ae_of_all _ fun s=> pearl X i R a q κ b D hp hs h hv hr hk s (hh s))
end pier
end YM.PhysicalNext.Repeat.Baffle
