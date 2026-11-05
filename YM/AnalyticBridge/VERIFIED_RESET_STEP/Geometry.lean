import YM.AnalyticBridge.VERIFIED_RESET_STEP.Higher
import YM.AnalyticBridge.VERIFIED_RESET_STEP.Quadratic
import YM.Push.ABSOLUTE_SUMS.Basic




/-!
# Uniform quotes for raw row and projected-residual lengths and supports

Pre-output orientation convention; no favorable wrap discard. Single-step
exponent reserve is just on EARLY products, not a smaller admissible class
for the next step. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.VerifiedReset
open Function Filter Set Lattice Wilson RG Push.AbsoluteSums Extra.Iteration Next.Scheduling
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {n : Side} {p : BudgetPoint}

namespace Geo
variable (p : BudgetPoint) (R : PathData G)

def anchorTile (o : Site n) := halo p.B {o}
lemma tiles (o : Site n) : coverNumber p.B (anchorTile p o) ≤ 81 := by simpa [anchorTile] using Corona.tile o 1 p.B p.B_pos
lemma enlarge (a : RegularAddress n) (hb : 2 ≤ p.B) : coverNumber p.B (expand a) ≤ coverNumber p.B a.support + 81 := by
  apply (Corona.meets_sum a.anchor (halo_subset 2 _ (Finset.mem_singleton_self _)) p.B).trans
  exact Nat.add_le_add_left ((Corona.cover_mono (Corona.halo_mono hb (Finset.Subset.refl _)) p.B).trans (tiles p a.site)) _
lemma enlarged_dist (a : RegularAddress n) (x : Site n) (hx : x∈expand a) :
    separation x a.site ≤ (4*p.B+2)*(1+coverNumber p.B a.support) := by
  rcases Finset.mem_union.mp hx with he|he
  · have h := Corona.extent _ p.B he a.anchor
    rw [Nat.mul_comm] at h; rw [Nat.mul_add,Nat.mul_one]; omega
  obtain ⟨_,ht,h⟩ := halo_spec.mp he; rw [Finset.mem_singleton.mp ht,separation_comm] at h
  exact h.trans (Nat.le_trans (by omega : 2 ≤ 4*p.B+2) (Nat.le_mul_of_pos_right _ (by omega)))

def lowCount : ℕ := 85
lemma low_geometry (d : Low) (x : Site n) : p.B * coverNumber p.B (d.home R p x) ≤ p.B*lowCount + d.length R := by
  unfold Low.home Low.length
  have h := Nat.mul_le_mul_left p.B (tiles p x)
  cases e : d.2 with
  | inl j => dsimp; exact h.trans (Nat.mul_le_mul_left p.B (by decide))
  | inr j =>
    dsimp only [Sum.elim_inr]
    have t := halo_subset p.B _ (Finset.mem_singleton_self x)
    apply (Nat.mul_le_mul_left p.B (Corona.meets_sum (Finset.mem_union_left _ t) (root_in _ x) p.B)).trans
    rw [Nat.mul_add]; apply le_trans (Nat.add_le_add
      (Nat.mul_le_mul_left p.B (Corona.meets_sum t (root_in _ x) p.B)) (Wages.walked (Low.right R d j) x p.B p.B_pos))
    rw [Nat.mul_add]; have hl := Wages.walked (Low.left R d j) x p.B p.B_pos
    unfold anchorTile at h; unfold lowCount; omega
lemma low_dist (d : Low) {x y : Site n} (hx : y∈ d.home R p x) : separation y x ≤ p.B*(1+d.length R) := by
  have hb := p.B_pos
  have hu (h : y∈halo p.B {x}) : separation y x ≤ p.B := by rw [separation_comm]; simpa only [halo_spec,Finset.mem_singleton,exists_eq_left] using h
  unfold Low.home at hx; unfold Low.length; cases he : d.2 <;> rw [he] at hx
  · exact (hu hx).trans (Nat.le_mul_of_pos_right _ (by omega))
  dsimp only [Sum.elim_inr]; rcases Finset.mem_union.mp hx with h|h
  · rcases Finset.mem_union.mp h with h|h
    · exact (hu h).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (slot_length _ _ h).trans (Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ hb))
  exact (slot_length _ _ h).trans (Nat.le_trans (by omega) (Nat.le_mul_of_pos_left _ hb))

def highCount : ℕ := 9
lemma high_geometry (d : High) (x : Site n) : p.B * coverNumber p.B (d.home R x) ≤ p.B*highCount + d.length R := by
  have h := Wages.traversed (d.term R) x p.B p.B_pos
  rcases High.significant d with hr|hr <;> simp only [hr] at h <;> unfold High.home High.length highCount <;> omega

variable (G)
def Width (c : Clip) (σ : ℝ) := 0 < σ ∧ 12 ≤ c.relaxation*σ ∧ (p.supportExponent+1) / p.B ≤ σ/4

def lowerSize (c : Clip) (C : ℝ) := Fintype.card PlaqAxes * (c.direct + C*C)
lemma lower_budget {c σ C Λ} (h : R.Bounds c σ C Λ) :
    SumBudget (fun d : Low => |d.mark R c| * Real.exp (σ*d.length R)) (lowerSize c C) := by
  have hd := c.quadratic_pos
  apply Cost.product (Cost.finite _ (by nlinarith))
  intro a
  refine Cost.sum (by simpa [Low.mark,Low.length,abs_of_pos hd] using Cost.finite (α:=Unit) c.direct hd.le) ?_
  have he := budget_prod (h.rows a) (h.rows a); convert he using 2 with d
  simp [Low.mark,Low.length,Low.left,Low.right,mul_add,Real.exp_add]; ring

def highFee (k : ℕ) (p : BudgetPoint) (σ : ℝ) := Wages.startup G k p.power p.order * momentPrice (Wages.grade k p.power p.order) (σ/2)
def both p σ := highFee G 3 p σ + highFee G 4 p σ
lemma highFee_pos (p k) {σ : ℝ} (h : 0 < σ) : 0 < highFee G k p σ := by
  have := Wages.slot_ge G p.power p.order 0; have := momentPrice_pos (Wages.grade k p.power p.order) (half_pos h)
  unfold highFee Wages.startup; positivity
lemma both_pos (p) {σ : ℝ} (h : 0 < σ) : 0 < both G p σ := add_pos (highFee_pos G p 3 h) (highFee_pos G p 4 h)
lemma high_allow (d : High) {σ : ℝ} (hs : 0 < σ) : High.price R d p * Real.exp ((σ/2)*d.length R) ≤
    both G p σ * ((High.term R d).budget σ) := by
  have := Wages.slot_ge G p.power p.order 0
  have h := highFee_pos G p (High.arity d) hs
  let a := High.term R d
  have hA : 0 ≤ a.budget σ := by unfold Atom.budget Atom.magnitude; positivity
  let g := Wages.grade d.arity p.power p.order
  let v := Wages.startup G d.arity p.power p.order
  have hn : 0 ≤ v*a.magnitude := by unfold v Wages.startup Atom.magnitude; positivity
  have he := mul_le_mul_of_nonneg_left (spendMoment g (half_pos hs) (Nat.cast_nonneg a.length)) hn
  have hle : highFee G d.arity p σ ≤ both G p σ := by
    unfold both; rcases d.significant with hi|hi <;> rw [hi] <;> linarith only [highFee_pos G p 3 hs, highFee_pos G p 4 hs]
  calc _ ≤ (v*a.magnitude*(momentPrice g (σ/2) * Real.exp ((σ/2)*a.length))) * Real.exp ((σ/2)*a.length) := by
            rw [High.price,add_comm (High.length R d:ℝ)]; exact mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
       _ = highFee G d.arity p σ * a.budget σ := by
            unfold Atom.budget; rw [show σ*(a.length:ℝ)=σ/2*a.length+σ/2*a.length by ring,Real.exp_add]; unfold highFee v g; ring
       _ ≤ _ := mul_le_mul_of_nonneg_right hle hA
lemma high_budget {c σ C Λ} (h : R.Bounds c σ C Λ) :
    SumBudget (fun d => High.price R d p * Real.exp ((σ/2)*d.length R)) (both G p σ * (C+C)) := by
  apply budget_mono (budget_scale (both_pos _ p h.width).le (f:=fun d => (High.term R d).budget σ) (Cost.sum h.three h.four))
  · exact fun i => mul_nonneg (High.price_nn ..) (Real.exp_pos _).le
  exact fun d => high_allow G p R d h.width

def rowDegree (p : BudgetPoint) : ℕ := (p.power+1)*p.order*2
lemma rowCost_shape (p : BudgetPoint) (l : ℕ) : rowCost G p l = rowCost G p 0 * (1+(l:ℝ))^rowDegree p := by
  simp only [rowCost,Wages.slotCost, Wages.margin,rowDegree,mul_pow, pow_mul,Nat.cast_zero,zero_add,one_pow,mul_one]
  rw [add_comm (l:ℝ)]; ring
lemma low_vs (l : ℕ) : lowCost G p l ≤ lowCost G p 0*(1+(l:ℝ))^rowDegree p := by
  simp only [lowCost,rowCost_shape G p l]
  have := faceCost_nonneg G p; have := pair_nonneg G p
  have he := mul_le_mul_of_nonneg_left (one_le_pow₀ (by simp : (1:ℝ) ≤ 1+(l:ℝ)) (n:=rowDegree p)) (show 0 ≤ (2:ℝ)⁻¹ * pairBill G p + faceCost G p by positivity)
  linarith

def lowFee (σ : ℝ) := lowCost G p 0 * momentPrice (rowDegree p) (σ/2)
lemma lowFee_nonneg {σ : ℝ} (hs : 0 < σ) : 0 ≤ lowFee G p σ := mul_nonneg (low_nonneg ..) (momentPrice_pos _ (half_pos hs)).le
lemma low_budget {c σ C Λ} (h : R.Bounds c σ C Λ) : SumBudget
    (fun d : Low => |d.mark R c| * lowCost G p (d.length R) * Real.exp ((σ/2)*d.length R)) (lowFee G p σ * lowerSize c C) := by
  apply Cost.mono (budget_scale (lowFee_nonneg G p h.width) (lower_budget G R h))
  · exact fun i => mul_nonneg (mul_nonneg (abs_nonneg _) (low_nonneg ..)) (Real.exp_pos _).le
  intro d; let l := d.length R
  have ht := (low_vs G p l).trans (mul_le_mul_of_nonneg_left (spendMoment _ (half_pos h.width) (Nat.cast_nonneg _)) (low_nonneg ..))
  apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (abs_nonneg (d.mark R c))) (Real.exp_pos _).le)
  rw [show σ*((d.length R):ℝ)=σ/2*l+σ/2*l by unfold l; ring,Real.exp_add,lowFee]
  unfold l; ring_nf; rfl

lemma kept_debit {c σ C Λ} (hW : Width p c σ) (h : R.Bounds c σ C Λ) : SumBudget
    (fun d : Low => Real.exp ((d.length R : ℝ)/c.relaxation) * |d.mark R c| * Real.exp ((3*σ/4)*d.length R)) (lowerSize c C) := by
  apply Cost.mono (lower_budget G R h) (fun _ => by positivity) fun d => ?_
  rw [mul_comm (Real.exp _) |d.mark R c|, mul_assoc,← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (abs_nonneg _)
  have ht := hW.2.1
  have hi := mul_le_mul_of_nonneg_right (show (1:ℝ)/c.relaxation ≤ σ/4 from (div_le_iff₀ c.radius_pos).mpr (by linarith))
    (Nat.cast_nonneg (α:=ℝ) (d.length R))
  rw [div_mul_eq_mul_div,one_mul] at hi; linarith
end Geo
end YM.AnalyticBridge.VerifiedReset
