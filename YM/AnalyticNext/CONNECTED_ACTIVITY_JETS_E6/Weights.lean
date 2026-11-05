import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Numerics
import YM.Bid.Craft
import YM.Push.RELAY_DIFFERENCE.SingleMajorant


/-!
# Inherited Hit budgets for real sector expansions

E first component sum; exploit the per-label supremum and per-anchor
actual ℓ path sums. Leave room for differentiated invoices in the
output tests (`length` or old cover, in addition to cover in *coarse*
coordinates). Keep the directions and multiplicities in actual
address spaces; still needs nonlinear estimates and matching when
installing the estimates. `PathPrices` applies these statements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6
open Filter Lattice RG Pressure Pressure.Stores Wilson Finset MeasureTheory
open Push AbsoluteSums AbsoluteSums.Paths AbsoluteSums.Footprint Reserves
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n c f : Side} {ι κ : Type*}

/-- Optional hit invoice (w nonnegative on the entire alphabet, extra
in Nat units). No b assigned here for possible *packets*. ε paid in
addition to the cover exponent a. -/
structure Sales (B : ℕ) (a ε : ℝ) (X : ι → Support c) (w : ι → ℝ) (e : ι → ℕ) (γ : ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  hit : Ac.Hit X B (tariff w (fun i => (e i:ℝ)) (fun _ => 0) ε) a γ

namespace Sales
variable {X : ι → Support c} {w z : ι → ℝ} {e : ι → ℕ} {B M l : ℕ} {a ε δ γ γ' : ℝ}

lemma raise (h : Sales B a ε X w e γ) (hg : γ ≤ γ') : Sales B a ε X w e γ' :=
  ⟨h.nonneg, fun x => budget_loosen (h.hit x) hg⟩

lemma shift (h : Sales B a ε X w e γ) {A : ℝ} (hA : 0 ≤ A) (hz : ∀ i, 0 ≤ z i)
    (hv : ∀ i, z i ≤ A*w i) : Sales B a ε X z e (A*γ) := by
  refine ⟨hz,fun x => budget_mono (budget_scale hA (h.hit x)) ?_ ?_⟩
  · intro i; split <;> first | exact mul_nonneg (mul_nonneg (hz i) (Real.exp_pos _).le) (Real.exp_pos _).le | exact le_rfl
  intro i; split
  next hh =>
    rw [tariff,tariff,← mul_assoc,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hv _) (Real.exp_pos _).le) (Real.exp_pos _).le
  next hh => rw [mul_zero]

lemma atom (h : Sales B a ε X w e γ) (ha : 0 ≤ a) (hε : 0 ≤ ε) (i : ι) (he : (X i).Nonempty) : w i ≤ γ := by
  obtain ⟨x,hx⟩ := he
  have ht := budget_single (h.hit x) i
  simp only [hx,↓reduceIte,tariff,add_zero] at ht
  exact le_trans (le_mul_of_one_le_right (h.nonneg i) (Real.one_le_exp (by positivity)))
    ((le_mul_of_one_le_right (mul_nonneg (h.nonneg i) (Real.exp_pos _).le)
      (Real.one_le_exp (by positivity))).trans ht)

/-- For repeated first arguments with the SAME physical support bound (test
separately, still charge all copies). -/
lemma price_fst [Fintype κ] (w : κ × ι → ℝ) (X : κ × ι → Support c) (e : κ × ι → ℕ) (p : κ → ℝ)
    (h : ∀ j : κ, Sales B a ε (fun i => X (j,i)) (fun i => w (j,i)) (fun i => e (j,i)) (p j)) :
    Sales B a ε X w e (∑ j, p j) := by
  refine ⟨fun j => (h j.1).nonneg j.2,fun x => budget_rows _ p ?_ ?_⟩
  · intro j; exact (h j).hit x
  exact budget_finite (fun i => budget_nonneg ((h i).hit x)) le_rfl

lemma together {Y : κ → Support c} {u : κ → ℝ} {d : κ → ℕ}
    (h : Sales B a ε X w e γ) (hk : Sales B a ε Y u d γ') :
    Sales B a ε (Sum.elim X Y) (Sum.elim w u) (Sum.elim e d) (γ+γ') := by
  refine ⟨fun i => ?_,?_⟩
  · cases i <;> first | exact h.nonneg _ | exact hk.nonneg _
  convert Labels.together X Y B h.hit hk.hit using 1; ext i
  cases i <;> rfl

lemma rotated (h : Sales B a ε X w e γ) (s : Signed) (y : Site c) (ha : 0 ≤ a) :
    Sales B a ε (fun i => (X i).image (affine s y)) w e γ := by
  let r : Equiv.Perm (Site c) := RelayDifference.Single.rotor s y
  have he (i : Site c) : affine s y i = r i := rfl
  refine ⟨h.nonneg,?_⟩
  intro x
  obtain ⟨x,rfl⟩ := r.surjective x
  have hp i : 0 ≤ tariff w (fun i => (e i:ℝ)) (fun _ => 0) ε i := mul_nonneg (h.nonneg i) (Real.exp_pos _).le
  refine budget_mono (h.hit x) (fun i => ?_) fun i => ?_
  · dsimp only; split <;> first | exact mul_nonneg (hp i) (Real.exp_pos _).le | exact le_rfl
  dsimp only; split
  next hx =>
    obtain ⟨j,hj,ht⟩ := mem_image.mp hx
    rw [he] at ht
    rw [if_pos (show x∈X i from r.injective ht ▸ hj)]
    exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_left
      (by exact_mod_cast RelayDifference.Single.cover_price s y (X i) B) ha)) (hp _)
  next hx => exact (h.hit x).1 _

/-- Old anchor weights become new sales after keeping the extra revenue
for polynomial estimates. -/
lemma anchored_sale {Y : ι → Support f} (p : Ratio c f) (o : ι → Site f) (ho : ∀ i, o i∈Y i)
    (h : Anchored o w (fun i => coverNumber M (Y i)) δ γ) (hw : ∀ i,0 ≤ w i)
    (he : ∀ i, X i ⊆ enlargement p l B (Y i)) (hB : 0 < B) (hM : M ≤ 2*B)
    (hr : reserve (δ-2*ε) a (conversion p l) ε)
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (hz : ∀ i,0 ≤ z i ∧ z i ≤ C*w i*(1+(coverNumber M (Y i):ℝ))^d) :
    Sales B a ε X z (fun i => coverNumber M (Y i))
      (payment (p.count.val^4) (extentCost l B) d ε C γ a (preCost l)) := by
  let e := fun i => coverNumber M (Y i)
  let v := tariff w (fun i => (e i:ℝ)) (fun _ => 0) ε
  have ht : Anchored o v e (δ-2*ε) γ := by
    intro x
    convert h x using 1; ext i
    simp only [v,tariff,add_zero,sub_mul,mul_assoc,← Real.exp_add]
    by_cases hk : o i=x <;> simp [hk,e]
  refine ⟨fun i => (hz i).1, coarsen p l B M Y o ho v (fun i => mul_nonneg (hw _) (Real.exp_pos _).le) ht
    X he hB hM hC hr d _ (fun i => mul_nonneg (hz i).1 (Real.exp_pos _).le) (fun i => ?_)⟩
  unfold tariff v tariff
  exact (mul_le_mul_of_nonneg_right (hz i).2 (Real.exp_pos _).le).trans_eq (by unfold e; ring)

/-- Buy extended vertex support, polynomial and extra (`2ε` length
reserve), from TRUE supplied path budget. -/
lemma paths {r : ℕ} (p : Ratio c f) (A : ι → Fin r → Slot) (hw : ∀ i,0 ≤ w i)
    (h : SumBudget (fun i => w i*Real.exp (δ*(length (A i)))) γ)
    (X : Site f × ι → Support c) (hy : ∀ i, X i ⊆ enlargement p l B (bundle i.1 (A i.2)))
    (hs : 0 < δ-2*ε) (hB : 0 < B) (hr : reserve (δ-2*ε) a (legFee p l B) ε)
    (d : ℕ) {C : ℝ} (hC : 0 ≤ C) (z : Site f × ι → ℝ) (hz : ∀ i,0 ≤ z i ∧ z i ≤ C*w i.2*(1+ (length (A i.2):ℝ))^d) :
    Sales B a ε X z (fun i => length (A i.2))
      (payment (p.count.val^4) (originFee l B) d ε C γ a (baseFee (d:=r) p l)) := by
  refine ⟨fun i => (hz i).1,?_⟩
  let v := tariff w (fun i => (length (A i):ℝ)) (fun _ => 0) ε
  have hv : SumBudget (fun i => v i*Real.exp ((δ-2*ε)*(length (A i)))) γ := by
    convert h using 1; ext i
    simp [v,tariff,mul_assoc,sub_mul,← Real.exp_add]
  let Z := tariff z (fun i => (length (A i.2):ℝ)) (fun _ => 0) ε
  intro x
  have hg i : Z i ≤ C*v i.2*(1+(length (A i.2):ℝ))^d := by
    unfold Z tariff v tariff
    exact (mul_le_mul_of_nonneg_right (hz i).2 (Real.exp_pos _).le).trans_eq (by ring)
  simpa only [Nat.zero_le,↓reduceIte,pow_zero,mul_one] using! bundle_hit p l B A v hs
    (fun i => mul_nonneg (hw _) (Real.exp_pos _).le) hv X hy hB hC hr d Z
    (fun i => mul_nonneg (hz i).1 (Real.exp_pos _).le) hg 0 x
end Sales

namespace Rate
-- Post-L powers; the constants don't constrain the application formulas.
variable {G : Gauge} {L : Side} {a b : ℝ} {C D : ℝ → ℝ} {B : ℝ → ℕ}

lemma transfers (u v : ℕ) : Rate G L 0 (fun x => ((u*radiusB x+v:ℕ):ℝ)) := by
  have hh := ((Rate.radius_price (G:=G) (L:=L)).mul_left (u:ℝ)).add (Rate.const (v:ℝ))
  simpa using hh

lemma payment (h : Rate G L a C) (g : Rate G L b D) (hp : Rate G L 0 (fun x => (B x:ℝ)))
    (P k : ℕ) (ε A v : ℝ) : Rate G L (a+b) (fun x => Footprint.payment P (B x) k ε (C x) (D x) A v) := by
  have he : Rate G L 0 (fun x => (spread P (B x):ℝ)) := by
    have ht := (((hp.mul_left 2).add (Rate.const 1)).pow 4).mul_left (P:ℝ)
    simpa [Footprint.spread,Animals.ballCost,two_mul] using ht
  unfold Footprint.payment degreeIncome
  rw [add_comm a b]
  have hf := (((g.mul_left (Real.exp (A*v))).mul h).mul he).mul_right
    (ε⁻¹^(4+k) * (4+k).factorial * Real.exp ε)
  rw [add_zero] at hf
  exact hf.mul_right _
end Rate
end YM.ConnectedActivityE6
