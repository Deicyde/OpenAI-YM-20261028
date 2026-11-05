import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plise

/-!
# Exact Jacobian scoreboard on lens recoil.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical ENNReal
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {k : Finset ℕ} {R : Rep G f} {z : Air f G} {E : Type}
variable {a A α β γ d η σ W s b μ r p q C C' v : ℝ} {j n l : ℕ} {Ñ : ChartRatio G}
variable (B : Finset (Bond f)) (X : Coat T F) (h : Canary G d A) (hp : 0<β) (V : Config G c) (he : Drivable X d A V)
def jacL (d β : ℝ) (V : Config G c) (z : Air f G) := ∏ i∈B,steerJ X d (worldZ X β z) V i

def blockM (d β : ℝ) (V : Config G c) (z : Air f G) : (B→G.Color) →L[ℝ] (B→G.Color) :=
    ContinuousLinearMap.pi fun i=> ContinuousLinearMap.comp
      (Eider.pax G X.χ d (G.mat (action X V i.val)) (worldZ X β z i.val)) (ContinuousLinearMap.proj i)

include h he hp
lemma blocks (z : Air f G) : HasFDerivAt (pitch B X d β V)
    (((stereo B G).symm.toContinuousLinearMap.comp (blockM B X d β V z)).comp (stereo B G).toContinuousLinearMap) (Pond.swim (lensS B G) z) := by
  let f (b:B→G.Color) i:= chore X d β V i.val (b i)
  let T:= stereo B G; let p:=Pond.swim (lensS B G) z
  have he : HasFDerivAt f (blockM B X d β V z) (T p) := hasFDerivAt_pi.mpr fun i=>
    ((has_chore X h hp V he i.val (T p i)).comp (f:=fun x:B→G.Color => x i) (T p) (hasFDerivAt_apply i (T p)))
  rw [show pitch B X d β V=(T.symm ∘ f) ∘ T from funext fun z=> quirk ..]
  exact ((T.symm.hasFDerivAt).comp (T p) he).comp p T.hasFDerivAt
lemma almanac (z : Air f G) : (fderiv ℝ (pitch B X d β V) (Pond.swim (lensS B G) z)).det=jacL B X d β V z := by
  let Z:= stereo B G; let f:= blockM B X d β V z
  rw [(blocks B X h hp V he z).fderiv]
  have hh : ((Z.symm.toContinuousLinearMap.comp f).comp Z.toContinuousLinearMap).det=f.det := by
    rw [ContinuousLinearMap.det]; change LinearMap.det (_∘ₗ _)=_
    exact LinearMap.det_conj f.toLinearMap Z.symm.toLinearEquiv
  unfold jacL; rw [hh,← prod_coe_sort]; dsimp only [f]; unfold blockM; rw [ContinuousLinearMap.det_pi]; rfl
omit hp h in
lemma jac_pos (β : ℝ) (z : Air f G) : 0<jacL B X d β V z := Finset.prod_pos
    (fun i _=> ((he.good i).2.2 ((worldZ X β z) i)).2)
lemma gyre (f' : Body (↥(lensS B G)) → ℝ) : (∫ t,f' t) =
    ∫ t,jacL B X d β V (Pond.spill (lensS B G) t)*f' (pitch B X d β V t) := by
  let I:= lensS B G; let g:= pitch B X d β V
  have hh (z : Body (↥I)) : DifferentiableAt ℝ g z := by
    nth_rw 1 [← Pond.settled I z]; exact (blocks B X h hp V he _).differentiableAt
  have hi:= Flux.across B X h hp V he
  have hF:= integral_image_eq_integral_abs_det_fderiv_smul volume (s:=Set.univ) MeasurableSet.univ (fun x _=>
    (hh x).hasFDerivAt.hasFDerivWithinAt) hi.1.injOn f'
  rw [Set.image_univ, Set.range_eq_univ.mpr hi.2,setIntegral_univ,setIntegral_univ] at hF
  refine hF.trans (integral_congr_ae (ae_of_all _ fun z=>?_))
  let v:=Pond.spill I z
  have hp := almanac B X h hp V he v; unfold v I at hp; rw [Pond.settled] at hp
  change |(fderiv ℝ (pitch B X d β V) z).det| * _=_; rw [hp,abs_of_pos (jac_pos B X V he ..)]
end YM.ConnectedActivityE6.Blaze.Flux
