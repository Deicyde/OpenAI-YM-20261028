import YM.UVExtension.Wick.Sliding

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a p q : ℝ} {z : Air f G} {Y : Config G c}
open Animals
-- The rectangular guard is used for continuation. Real success in the full bands is checked separately.
def aisle (x : ℝ) := {z:ℂ | x/2 < z.re ∧ z.re < 2*x ∧ |z.im| < x ^ (99/100:ℝ)}
lemma open_aisle (x:ℝ):IsOpen (aisle x) := (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt Complex.continuous_im.abs continuous_const))
lemma breath {x : ℝ} (hp : 0<x) {z : ℂ} (hz : z∈aisle x) : 0<z.re:= (half_pos hp).trans hz.1

def softR (_G:Gauge) (_L:Side) (b d:ℝ) := b^(99/100:ℝ)/(d/2)
lemma aisles (G:Gauge) (L:Side) (m:ℝ) (hp:0<m) : ∀ᶠ x:ℝ in atTop, ∀ (c f:Side) (S:StepData c f) (X:Support c) (z:ℂ),
    S.patch.L=L→ z∈ aisle (betaF G x L) → 0≤ Real.log (‖z‖/z.re) ∧ Real.log (‖z‖/z.re) ≤ 1 ∧ ‖z‖/z.re ≤2 ∧
    permag z (Fintype.card (↥(podium S G X (radiusB x)))) ≤ Real.exp (m*coverNumber (radiusB x) X) := by
  let v x:= softR G L (betaF G x L) (betaF G x L)
  have he:Rate G L (99/100-1) v:= by
    have hh : Rate G L (99/100-1) (fun x=> 2*(betaF G x L)^(99/100-1:ℝ)) := Rate.power.mul_left _
    refine hh.congr ?_; filter_upwards [Delay.shift_pos G L] with x hx
    unfold v softR; rw [Real.rpow_sub hx]; rw [Real.rpow_one]; ring
  have hf : Rate G L 0 (fun x=> (Animals.ballCost (radiusB x):ℝ)) := by simpa only [one_mul,add_zero] using! width_rate G L 1 0
  let w x:=((ballCost (radiusB x):ℝ)*Itinerary.density L*Fintype.card G.ColorIndex)/2
  have hW : Rate G L 0 w := by unfold w; simpa only [div_eq_mul_inv] using! (((hf.mul_right _).mul_right _).mul_right _)
  filter_upwards [Delay.shift_pos G L,he.below (by norm_num) 1 zero_lt_one,(hW.mul he).below (by norm_num) m hp] with x hx hv hV c f S X z hL hz
  let d:= betaF G x L; have hr:= breath hx hz
  let B:=radiusB x
  have hR: 1 ≤ ‖z‖/ z.re := (one_le_div hr).mpr (Complex.re_le_norm z)
  have hD: ‖z‖/ z.re-1 ≤ v x := by
    have hp : ‖z‖-z.re ≤ |z.im|:= by have h:= Complex.norm_le_abs_re_add_abs_im z; rw [abs_of_pos hr] at h; linarith
    unfold v softR
    calc
      _ = (‖z‖-z.re)/z.re := by field_simp
      _ ≤ (betaF G x L ^ (99/100:ℝ))/ z.re := div_le_div_of_nonneg_right (hp.trans hz.2.2.le) hr.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (half_pos hx) hz.1.le
  have ha := Real.log_nonneg hR; have hu : Real.log (‖z‖/ z.re) ≤ v x:= (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hR)).trans hD
  have hv':v x≤1:= (le_abs_self _).trans hv
  refine ⟨ha,hu.trans hv',by linarith,?_⟩
  let I:= edgesM S X B; let Z:= univ.filter fun i:Bond f=> atEdge S i∈X; let n:=coverNumber B X
  have hI : I.card≤ X.card *Itinerary.density L:= (Finset.card_le_card (show I ⊆ Z from fun i hi=> mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2 (atEdge S i) (by simp)⟩)).trans (hL ▸ (perch S X))
  have he : podium S G X B=lensS I G:= (chargedU ..).symm
  have hp : (Fintype.card (↥(podium S G X B)):ℝ)≤ n*((Animals.ballCost B:ℝ)*Itinerary.density L*Fintype.card G.ColorIndex) := by
    rw [he]; have h : I.card ≤ n*Animals.ballCost B*Itinerary.density L:= hI.trans (Nat.mul_le_mul_right _ (brood X B))
    have hh : Fintype.card (↥(lensS I G)) ≤ n*(Animals.ballCost B*Itinerary.density L*Fintype.card G.ColorIndex):= by
      rw [Fintype.card_coe, lensS, card_product,card_univ]; exact (Nat.mul_le_mul_right _ h).trans_eq (by ring)
    exact_mod_cast hh
  apply Real.exp_monotone; apply le_trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (by norm_num : (0:ℝ) ≤ 2)) ha)
  have he:w x* Real.log (‖z‖/z.re)≤ m:= (mul_le_mul_of_nonneg_left hu (show 0≤w x from by unfold w; positivity)).trans ((le_abs_self _).trans hV)
  exact (le_of_eq (by unfold w B; ring : _=(n:ℝ)*(w x* Real.log (‖z‖/z.re)))).trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans_eq (mul_comm ..)) -- simplify

lemma permits (G:Gauge) (L:Side) : ∀ᶠ x:ℝ in atTop, ∀ (c f:Side) (S:StepData c f) (z:ℂ),
    S.patch.L=L→ z∈aisle (betaF G x L) → 0<z.re ∧ ‖z‖/z.re ≤2 := by
  filter_upwards [aisles G L 1 zero_lt_one,Delay.shift_pos G L] with x hx hp c f S z he hk
  exact ⟨breath hp hk,hx c f S ∅ z he hk |>.2.2.1⟩
end YM.UVExtension.Wick
