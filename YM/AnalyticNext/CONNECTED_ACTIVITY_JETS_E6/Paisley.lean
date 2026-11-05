import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Eskim
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Plateau
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Thistle

/-!
# Truncation rendering for convergence of transported integral. Polar only!
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Flux
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary Scroll Vine Polar Frond Corona Brush   Tablet Strokes Quill Bid Matter
open Packets  Silica Poll Pond  Eider
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G}
variable {R : Rep G f} {A a α β B C p : ℝ}

def prune (A : ℝ) (b : G.Color) := if ‖b‖≤3*A then b else (3*A/‖b‖) • b

lemma pruned (b : G.Color) (hA : 0<A) (he : ¬ ‖b‖≤3*A) : ‖prune A b‖=3*A := by
  have he:0<‖b‖:= lt_trans (by positivity : 0 < 3*A) (lt_of_not_ge he)
  unfold prune; rw [if_neg (by assumption),norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ 3*A/‖b‖)]; field_simp
lemma berries (b : G.Color) (hA : 0<A) : ‖prune A b‖ ≤ 3*A := by
  by_cases he: ‖b‖≤3*A
  · rw [prune,if_pos he]; exact he
  exact (pruned b hA he).le
variable (X : Coat T F) (h : Canary G A C) (U : Config G c)

include h
lemma braided (i : G.Color) (g : G.Mat) : Eider.plume G X.χ A g i=Eider.plume G X.χ A g (prune A i) ∧
    palm G X.χ A g i=palm G X.χ A g (prune A i) := by
  by_cases hp :‖i‖≤3*A
  · rw [prune,if_pos hp]; exact ⟨rfl,rfl⟩
  have hg: 2*A<‖i‖:= lt_trans (by linarith [h.warm] : 2*A<3*A) (lt_of_not_ge hp)
  have he : 2*A<‖prune A i‖ := by rw [pruned i h.warm hp]; linarith [h.warm]
  exact ⟨(Eider.cooler h X.χ hg.le g).trans (cooler h X.χ he.le g).symm,(duckling h X.χ hg g).trans (duckling h X.χ he g).symm⟩

-- `Compact body` leg. Chart surf. For all Y,Π
lemma fruit (u : Directions G f) {a : ℝ} (he : a ≤ A) : Transfer X (steer X A u U) (steer X A (fun i=>prune A (u i)) U) a := by
  refine ⟨fun i=>?_⟩; let v:=u i
  by_cases ht : ‖v‖≤3*A
  · left; unfold steer; dsimp only; rw [show prune A (u i)=u i from if_pos ht]
  have hT:3*A=‖prune A v‖ := (pruned v h.warm ht).symm
  have hv : 2*A≤‖v‖ := by rw [not_le] at ht; linarith [h.warm]
  have hp : 2*A≤‖prune A v‖ := by rw [← hT]; linarith [h.warm]
  right; unfold steer fleece; dsimp only; change a<‖v+_‖ ∧ a<‖prune A v+_‖
  change 2*A≤‖u i‖ at hv; change 2*A ≤‖prune A (u i)‖ at hp; unfold v at *; simp_rw [cooler h X.χ hv,cooler h X.χ hp,add_zero]; constructor <;> linarith [h.warm]

lemma thatch (a W : ℝ) (p : Molecule S) (l : ℕ) (Ñ : ChartRatio G) (hp : Drivable X A C U) (ha : 0<a*X.t)
    (hv : 8*a*X.t ≤ A/2) (hM : (vary X U).Noncrystal) (hH : Room P S T X.x) (hR : Intake P T X.x R) (z : Air f G) :
    let u:=worldZ X R.beta z; let Z:=vary X U; let w:=steer X A (fun i=>prune A (u i)) U
    Polar.floating Z a R W Ñ (course X A R.beta z U) (own p) l p=
      ∏ i∈p,Polar.ember Z a R W Ñ w (X.input u) (sweepZ Z R.beta w) (own p) l i := by
  intro u Z w; have he := conquered X h U u hp ha hv; let b := steer X A u U
  have hm : Transfer Z b w (4*a*X.t):= ⟨(fruit X h U u (a:=4*a*X.t) (by nlinarith only [hv,h.warm])).both⟩
  unfold floating; rw [show worldZ Z _ (course X A R.beta z U)=b from Silica.proceeds X _ hR.positive _ _]; apply prod_congr rfl
  intro i hi
  have hx:= (plastic (X:=Z) he (show 0<a*X.t from ha)).reeled hH W Ñ (own p) l hR i (course X A R.beta z U)
  exact hx.trans (Transfer.carries Z hm ha hH hM _ _ _ _ l _ i)
end YM.ConnectedActivityE6.Blaze.Flux
