import YM.Corona.Fit
import YM.Push.LOCAL_SPLITTING.Products



/-!
# Full cover reserve for products rooted at an external marked support

Per measured derivative order, only polynomial size overhead also for many factors at
shifted anchors. Tail/summability on `Finset`-indexed distinct-address packs (each
component must attach, ANY multiplicity of touches at the root counted); numbered
log occurrences will be inside some of these distinct addresses.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Function Filter Lattice Wilson RG Push.Local MeasureTheory 
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {ι : Type*} {B : BudgetPoint}

def deg (B : BudgetPoint) := B.order*(1+B.power)
def distanceCost (B : BudgetPoint) := (6*B.B+3:ℝ)^(B.order*B.power)
def productFee (B : BudgetPoint) (D : ℕ) := distanceCost B * (1+D : ℝ)^deg B

lemma distanceCost_pos : 1 ≤ distanceCost B := one_le_pow₀ (by linarith [show 0 ≤ (B.B:ℝ) by positivity])
lemma productFee_pos (D : ℕ) : 1 ≤ productFee B D := one_le_mul_of_one_le_of_one_le distanceCost_pos (one_le_pow₀ (by simp))

private lemma pays_extent (m D : ℕ) (h : m ≤ D) :
    (((m+1:ℕ):ℝ) * (1+(D*(4*B.B+2)+2*B.B:ℕ))^B.power)^B.order ≤ productFee B D := by
  have he : (1+((D*(4*B.B+2)+2*B.B:ℕ):ℝ)) ≤ (1+(D:ℝ))*(6*B.B+3) := by
    exact_mod_cast (show 1+(D*(4*B.B+2)+2*B.B) ≤ (1+D)*(6*B.B+3) by nlinarith)
  refine le_trans (b:=((1+(D:ℝ)) * ((1+D) * (6*B.B+3))^B.power)^B.order) ?_ ?_
  · gcongr; exact_mod_cast (show m+1 ≤ 1+D by omega)
  unfold productFee distanceCost deg; exact le_of_eq (by simp only [mul_pow, pow_mul]; ring)

lemma product_bound (s : Finset ι) (f : ι → Config G n → ℂ) (a : ι → ℝ) (X : ι → Support n)
    (b : ι → Site n) {o : Site n} {Y : Support n} {D : ℕ} (hp : ∀ i∈s,X i ⊆ Y)
    (hb : ∀ i∈s,b i∈Y) (ho : o∈Y) (hD : coverNumber B.B Y ≤ D) (h : s.card ≤ D)
    (hr : ∀ i∈s,B.Regular (X i) (f i)) (he : ∀ i∈s,B.supBounds (b i) (X i) (f i) (a i)) :
    B.supBounds o Y (∏ i∈s,f i) (productFee B D * ∏ i∈s,a i) := by
  let R := D*(4*B.B+2)+2*B.B
  have hh i (hi : i∈s) : separation (b i) o ≤ R := (Corona.extent Y B.B (hb i hi) ho).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ hD) _)
  exact bound_weaken (price_product s f a o b R hh X hp hr he).2 (mul_le_mul_of_nonneg_right
    (pays_extent _ _ h) (Finset.prod_nonneg fun i hi => (he i hi).1))

section Pack
variable (X : ι → Support n) (b : ℕ) (Y : Support n) (s : Finset ι)

def bounds := Y ∪ s.biUnion X









variable {s}



end Pack
end YM.Planned.Forced
