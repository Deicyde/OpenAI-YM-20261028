import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.QuadraticTilts
import YM.Next.SCHEDULE.GridCost
import YM.Next.SCHEDULE.Stadium

/-!
# Uniform joint tilt budget, value layer

Use on actual selected factors, including exponentials of remaining ratio
rows and using trigger-witness words **without** differentiating any hard
indicator. Each spelling hit test sees one such bound in a fixed
projection; scores and marked insertions may use a further whole-word
fee; track costs with extra anchors at their use too.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Centered
open Function MeasureTheory Filter Matrix
open Progress.StationaryScenes
open scoped Topology BigOperators ENNReal Matrix.Norms.Frobenius

/-- After tilting, retain this much coercivity in physical squared norm
units. Allocation of paid exponents is not in energy units (β). -/
structure Till where
  floor : ℝ
  expense : ℝ
  floor_pos : 0 < floor
  expense_nn : 0 ≤ expense

namespace Till
variable {n : Type*} [Fintype n] {A : Matrix n n ℝ} (t : Till)

def Safe (A : Matrix n n ℝ) := A.IsHermitian ∧ Green.Bottom A (t.floor+t.expense)

structure Tilt (n : Type*) where
  cap : ℝ
  tally : n → ℝ

def Tilt.Sound (b : Tilt n) := 0 ≤ b.cap ∧ ∀ i, 0 ≤ b.tally i

def sale (b : Tilt n) := b.cap * Real.exp ((t.floor⁻¹ * ∑ i, b.tally i)/2)

def Ticket (b : Tilt n) (v : n → ℝ) : ℝ := b.cap * Real.exp (tilt b.tally v/2)

lemma sale_nn {b : Tilt n} (h : b.Sound) : 0 ≤ t.sale b :=
  mul_nonneg h.1 (Real.exp_pos _).le

variable {ι : Type*} (Q : ι → Tilt n)

def occupied (s : Finset ι) := ∀ i, (∑ j ∈ s, (Q j).tally i) ≤ t.expense

/-- Any **one** set of factors may spend the exponential ticket under the
one actual Gaussian. Empty product also priced. -/
lemma consume [DecidableEq n] (hA : t.Safe A) (s : Finset ι) (hs : t.occupied Q s)
    (hu : ∀ j∈s, (Q j).Sound) {X : Type*} [NormedAddCommGroup X]
    (g : (n → ℝ) → X) (hg : AEStronglyMeasurable g (law A))
    (h : ∀ z, ‖g z‖ ≤ ∏ i∈s, Ticket (Q i) z) : Integrable g (law A) ∧
    (∫ z, ‖g z‖ ∂law A) ≤ ∏ i∈s, t.sale (Q i) := by
  let C := ∏ i∈s,(Q i).cap
  let d x := ∑ i∈s,(Q i).tally x
  have hC : 0 ≤ C := Finset.prod_nonneg fun i hi => (hu _ hi).1
  obtain ⟨he,hv⟩ := tilted (d:=d) t.floor_pos hA.1 hA.2 (fun x =>
    Finset.sum_nonneg fun i hi => (hu _ hi).2 _) hs
  have h z : ‖g z‖ ≤ C * Real.exp (tilt d z/2) := by
    apply (h z).trans_eq
    simp_rw [Ticket, Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_div]
    congr 3
    simp_rw [tilt,d, Finset.sum_mul, Finset.sum_comm (s:=s)]
  have hm := (he.const_mul C).mono' hg (Eventually.of_forall h)
  refine ⟨hm,(integral_mono hm.norm (he.const_mul C) h).trans ?_⟩
  rw [integral_const_mul]; apply (mul_le_mul_of_nonneg_left hv hC).trans_eq
  simp_rw [sale, Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.sum_div, ← Finset.mul_sum, d,
    Finset.sum_comm (t:=s)]; rfl

section rarity
variable (I : Finset n)

def hitTilt [DecidableEq n] (C δ u : ℝ) : Tilt n := ⟨C * Real.exp (-u*δ/2), fun i => if i∈I then u else 0⟩

variable [DecidableEq n] {δ u C : ℝ}

omit [Fintype n] in
lemma hitSound (hb : 0 ≤ C) (hu : 0 ≤ u) : (hitTilt I C δ u).Sound :=
  ⟨mul_nonneg hb (Real.exp_pos _).le,fun i => by
    dsimp only [hitTilt]; split <;> first | exact hu | exact le_rfl⟩





def ratioTilt (x : ℝ) : Tilt n := ⟨x*Real.exp (2*x),fun i => if i∈I then 4*x else 0⟩

omit [Fintype n] in
lemma ratioSound {x : ℝ} (h : 0≤x) : (ratioTilt I x).Sound :=
  ⟨by change 0 ≤ x*_; positivity,fun i => by dsimp only [ratioTilt]; split <;> positivity⟩



omit [Fintype n] [DecidableEq n] in
lemma exp_bound {x b : ℝ} (h : |x| ≤ b) : |Real.exp x-1| ≤ b*Real.exp b := by
  have hb := (abs_nonneg _).trans h
  have he := Real.add_one_le_exp (-x)
  rcases (abs_le.mp h) with ⟨hL,hR⟩
  rw [Real.exp_neg] at he
  have hy := mul_inv_cancel₀ (Real.exp_pos x).ne'
  apply abs_le.mpr; constructor
  · have H := Real.add_one_le_exp x; have hx := Real.one_le_exp hb
    nlinarith
  have H := mul_le_mul_of_nonneg_right he (Real.exp_pos x).le
  rw [inv_mul_cancel₀ (Real.exp_pos x).ne'] at H
  have hx := Real.exp_le_exp.mpr hR
  nlinarith [mul_le_mul_of_nonneg_right hR (Real.exp_pos x).le, mul_le_mul_of_nonneg_left hx hb]


end rarity
end Till
end YM.AnalyticNext.ConnectedActivity.Centered
