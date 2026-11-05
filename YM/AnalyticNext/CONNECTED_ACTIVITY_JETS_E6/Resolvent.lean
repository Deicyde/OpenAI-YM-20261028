import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Control
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Windows

/-!
# Joint precision prices

Schedule θ & its quoted radius fractionally decreasing before choosing beta.
Full vs varying window Pi. `G` exact inverses only cited in formulas for price,
not dependence in words. No-hole comparison/resum separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Window
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type*} {c : Side} {a : ι→Site c} {B m : ℕ} (D : Window a B) [DecidableEq ι] [Fintype ι]
variable {A : Matrix ι ι ℝ} {X η r : ℝ}

/-- Choose a universal dim after joint physical invoices, always ≤ 1. -/
def dim (r X : ℝ) := min 1 ((r/2)/X)
def band (η r X : ℝ) := dim r X * η

def payInv (r : ℝ) := (min 1 (r/2))⁻¹

def retain (η r X : ℝ) := band η r X /3

def payE (η r X : ℝ) (m : ℕ) := price0 (band η r X-2*retain η r X)*m*payInv r

def scraps (η r X : ℝ) (m B : ℕ) := Real.exp (-retain η r X*B)*(X*payE η r X m+1)

/-- Prices carry sign info. RoomProducer supplies needed geometry for controllers. -/
structure Allow (M : Matrix ι ι ℝ) (a : ι → Site c) (m : ℕ) (η r X : ℝ) : Prop where
  census : Census m a
  symmetry : IsHermitian M
  eta : 0 < η
  down : 0 < r
  fuel : 0 < X
  price : Rows a a M η X
  ground : Bottom M r

namespace Allow

omit [DecidableEq ι] in
lemma weather (h : Allow A a m η r X) : 0 < retain η r X ∧ 2*retain η r X < band η r X ∧ band η r X ≤ η := by
  have hf : 0 < dim r X := lt_min zero_lt_one (div_pos (half_pos h.down) h.fuel)
  have he : 0 < band η r X := mul_pos hf h.eta
  unfold retain; refine ⟨by linarith,by linarith,?_⟩
  exact mul_le_of_le_one_left h.eta.le (min_le_left ..)
omit [DecidableEq ι] in
lemma disc (h : Allow A a m η r X) : 0 ≤ payE η r X m := by
  have hf : 0 ≤ price0 (band η r X-2*retain η r X) :=
    tsum_nonneg fun i => by unfold rates0; positivity
  have hh : 0 < min 1 (r/2) := lt_min zero_lt_one (half_pos h.down)
  unfold payE payInv; positivity
omit [DecidableEq ι] in
lemma heap (h : Allow A a m η r X) (n : ℕ) : 0 ≤ scraps η r X m n := by
  have := h.disc; have := h.fuel; unfold scraps; positivity
omit [DecidableEq ι] in
lemma relented (h : Allow A a m η r X) : Price a a A (retain η r X) X := by
  obtain ⟨hf,hk,hp⟩ := h.weather
  exact increase (density _ _ _ h.symmetry h.price) ((by linarith : retain η r X ≤ band η r X).trans hp) le_rfl
omit [DecidableEq ι] in
lemma sub {κ : Type*} [Fintype κ] (h : Allow A a m η r X) (e : κ ↪ ι) : Allow (A.submatrix e e) (a ∘ e) m η r X := by
  refine ⟨?_, h.symmetry.submatrix _, h.eta,h.down,h.fuel,h.price.restrict _ e,h.ground.restrict e⟩
  intro Y; apply le_trans _ (h.census Y)
  let P := univ.filter fun i : κ => a (e i)∈Y
  change P.card ≤ (univ.filter (fun x=>a x∈Y)).card
  rw [← show (P.map e).card=P.card from card_map _]
  apply Finset.card_le_card
  intro i hi; obtain ⟨i,hk,rfl⟩ := mem_map.mp hi; exact mem_filter.mpr ⟨mem_univ _, (show a (e i)∈Y from ((mem_filter.mp (show i∈_ from hk)).2 : a (e i)∈Y))⟩

lemma initial (h : Allow A a m η r X) : A*A⁻¹=1 ∧ A⁻¹*A=1 ∧ ∀ i j,
    wt (band η r X) (a i) (a j)*|A⁻¹ i j| ≤ payInv r := by
  have hp : 0 < dim r X := lt_min zero_lt_one (div_pos (half_pos h.down) h.fuel)
  have hx := Green.inverse h.eta.le h.down hp.le (show dim r X ≤ 1 from min_le_left ..)
    ((le_div_iff₀ h.fuel).mp (min_le_right ..)) h.symmetry h.ground (density _ _ _ h.symmetry h.price) 0 le_rfl
  simpa only [band,payInv,zero_smul,add_zero,mul_one] using! hx

omit [DecidableEq ι] in
lemma move (h : Allow A a m η r X) {M : Matrix ι ι ℝ} (he : ∀ i j, wt (band η r X) (a i) (a j)*|M i j| ≤ payInv r) :
    Price a a M (2*retain η r X) (payE η r X m) := by
  have hu : 0 ≤ payInv r := inv_nonneg.mpr ((lt_min zero_lt_one (half_pos h.down)).le)
  refine ⟨Census.rows h.census a M hu h.weather.2.1 he, Census.rows h.census a _ hu h.weather.2.1 (fun i j => ?_)⟩
  rw [wt_symm]; exact he j i
lemma flatup (h : Allow A a m η r X) : Price a a A⁻¹ (retain η r X) (payE η r X m) :=
  increase (h.move h.initial.2.2) (by linarith [h.weather.1]) le_rfl

lemma primal (h : Allow A a m η r X) (D : Window a B) : Price a a (D.pad A) (2*retain η r X) (payE η r X m) := by
  apply h.move; intro i j; by_cases he : i∈D.take j
  swap
  · rw [D.outside _ _ _ he,abs_zero,mul_zero]; exact inv_nonneg.mpr ((lt_min zero_lt_one (half_pos h.down)).le)
  have hx := (h.sub (Embedding.subtype (·∈D.take j))).initial.2.2
  let k : ↥(D.take j) := ⟨i,he⟩; change wt _ _ _*|D.pad A k.val _| ≤ _; rw [D.inside]
  exact hx k ⟨j,D.here j⟩

lemma discrepancy (h : Allow A a m η r X) (D : Window a B) : Price a a (D.error A) (retain η r X) (scraps η r X m B) := by
  let k := retain η r X
  have hk : 0 < k := h.weather.1
  have ht := increase (density a A η h.symmetry h.price) (h.weather.2.1.le.trans h.weather.2.2) le_rfl
  have ha := paid_mul ht (h.primal D) (show 0≤ 2*k by positivity) h.fuel.le h.disc
  have hz : Price a a (D.error A) (2*k) (X*payE η r X m+1) := by
    rw [error,sub_eq_add_neg]; exact paid_add ha (spent_neg (one_pay ..))
  unfold scraps; rw [show -retain η r X=k-2*k by unfold k; ring]; refine spend_far hz B ?_ (show k≤2*k by linarith)
  intro i j H; exact D.mileage A i j (D.low _ _ H) (h.sub (Embedding.subtype (·∈D.take j))).initial.1

lemma breach (h : Allow A a m η r X) (D : Window a B) :
    Price a a (D.pad A-A⁻¹) (retain η r X) (payE η r X m * scraps η r X m B) := by
  have he : D.pad A-A⁻¹=A⁻¹ * D.error A := by rw [error,mul_sub,← mul_assoc,h.initial.2.1,mul_one,one_mul]
  rw [he]; exact paid_mul h.flatup (h.discrepancy D) h.weather.1.le h.disc (h.heap _)
end Allow
end YM.ConnectedActivityE6.Window
