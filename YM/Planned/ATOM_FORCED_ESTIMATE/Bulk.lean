import YM.Planned.ATOM_FORCED_ESTIMATE.Geometry
import YM.Planned.ATOM_FORCED_ESTIMATE.Mayer
import YM.Push.ABSOLUTE_SUMS.FiniteLog
import YM.Push.ABSOLUTE_SUMS.Reserves
import YM.Push.LOCAL_SPLITTING.Atoms




/-!
# Unforced vacuum first-system factors and the negative omitted addresses

For a distinguished forced INPUT there need not be a forced OUTPUT inventory in its
first component (only fine/noise seeds, for example). Later must test absence of every
unforced overlap with the marked component even in this case. Full factorials, full
before-mask derivatives on all occurrences (numbered vacuum tuple including repeated
use of the *same label*), complete true unions for omission supports. Uses the
AbsoluteSums real logarithm with its actual overlap relation on the true vacuum labels;
the exponent sign for the omitted addresses after moving the bulk is **negative**.
No assertion of first-integration localization or smallness of the unmarked prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.Forced
open Lattice Wilson RG Push.AbsoluteSums Push.Local Next.Foundations MeasureTheory Function
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side}

/-- Unforced first-gas population before the log or vacuum reclosure. -/
structure Bulk (G : Gauge) (n : Side) where
  address : ℕ → RegularAddress n
  val : ℕ → Config G n → ℝ

namespace Bulk
variable (T : Bulk G n) (B : BudgetPoint)

abbrev support (i : ℕ) := (T.address i).support
abbrev anchor (i : ℕ) := (T.address i).site

def read (V : Config G n) (i : ℕ) := masked B.threshold (T.support i) (T.val i) V

def cast (i : ℕ) (V : Config G n) := (T.val i V : ℂ)

/-- Vacuum test including coordinates and before-indicator derivatives through the
needed order. Complex formulation for reuse with signed source terms. -/
def Grants (w : ℕ → ℝ) := ∀ i, B.Regular (T.support i) (T.cast i) ∧
    B.supBounds (T.anchor i) (T.support i) (T.cast i) (w i)

theorem read_cast (V : Config G n) (i : ℕ) : (T.read B V i : ℂ) = masked B.threshold (T.support i) (T.cast i) V := by
  by_cases h : Healthy B.threshold (T.support i) V
  · simp only [cast,read, masked_eq _ _ _ _ h]
  simp only [read,masked_ne _ _ _ _ h,Complex.ofReal_zero]

variable {T B} in
theorem read_bound {w : ℕ → ℝ} (h : T.Grants B w) (V : Config G n) (i : ℕ) : ‖T.read B V i‖ ≤ w i := by
  rw [← Complex.norm_real, read_cast]
  by_cases hx : Healthy B.threshold (T.support i) V
  · rw [masked_eq _ _ _ _ hx]; exact (h i).2.2 V hx [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ hx, norm_zero]; exact (h i).2.1

abbrev Node := Ursell.Clusters ℕ
abbrev graph := Ursell.blocked T.support

def region (i : Node) := Ursell.unionOf T.support i.2
def center (i : Node) := T.anchor (i.2 none)
lemma region_has (i : Node) (j : Option (Fin i.1)) : T.support (i.2 j) ⊆ T.region i := Finset.subset_biUnion_of_mem (T.support ∘ i.2) (Finset.mem_univ j)
lemma anchored (i : Node) : T.center i ∈ T.region i := T.region_has _ _ ((T.address _).anchor)

lemma test : Ursell.Tests T.graph T.support := Ursell.literal_test _ (fun i => ⟨_,(T.address i).anchor⟩)

def load (i : Node) := ∑ j, coverNumber B.B (T.support (i.2 j))

def constant (i : Node) : ℝ := -Ursell.coefficient T.graph i.2 / (i.1+1).factorial

def negated (i : Node) := (T.constant i : ℂ) • ∏ j, T.cast (i.2 j)

def expTerm (i : Node) := mayer (T.negated i)

def withdraw (V : Config G n) (i : Node) := Real.exp (-Gas.term T.graph (T.read B V) i) - 1

lemma negated_mask (V : Config G n) (i : Node) : ((-Gas.term T.graph (T.read B V) i : ℝ):ℂ) =
    masked B.threshold (T.region i) (T.negated i) V := by
  unfold Gas.term negated constant
  rw [← show maskLinear B.threshold (T.region i) _ V = masked .. from rfl, map_smul,Pi.smul_apply,
    Complex.ofReal_neg,Complex.ofReal_div, Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_prod]
  simp only [read_cast]
  rw [← Finset.prod_apply (g:=fun j => masked B.threshold (T.support (i.2 j)) (T.cast (i.2 j))),product_masked]
  change _ = ((-(Ursell.coefficient T.graph i.snd):ℝ):ℂ) / _ * masked ..
  push_cast; unfold region Ursell.unionOf; simp only [comp_def]; ring

/-- Even when the cluster is counted only ONCE although meeting several kept supports,
it carries its whole mask and its same factorial-normalized weight. -/
lemma expTerm_mask (V : Config G n) (i : Node) : (T.withdraw B V i:ℂ) = masked B.threshold (T.region i) (T.expTerm i) V := by
  unfold withdraw; rw [Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_exp, T.negated_mask B V i, expTerm, ← mayer_mask]; rfl

def basePrice (w : ℕ → ℝ) (i : Node) := productFee B (T.load B i) * Ursell.clusters T.graph w i.2

lemma basePrice_eq (w : ℕ → ℝ) (i : Node) : ‖(T.constant i:ℂ)‖ * (productFee B (T.load B i) * ∏ j, w (i.2 j)) = T.basePrice B w i := by
  unfold basePrice constant Ursell.clusters; rw [Complex.norm_real, norm_div,norm_neg,Real.norm_eq_abs,
    Real.norm_of_nonneg (show 0 ≤ ((i.1+1).factorial:ℝ) by positivity)]; ring

private lemma products_regular {w : ℕ → ℝ} (h : T.Grants B w) (i : Node) : B.Regular (T.region i) (∏ j, T.cast (i.2 j)) :=
  regular_prod _ _ fun j _ => regular_larger (h (i.2 j)).1 (T.region_has ..)

private lemma covers (i : Node) (hi : Ursell.coefficient T.graph i.2 ≠ 0) : coverNumber B.B (T.region i) ≤ T.load B i := by
  have he := Ursell.connected_pay _ T.support B.B T.test i.2 zero_le_one hi
  simp only [Trees.currency,one_mul,← Real.exp_sum, Real.exp_le_exp,← Nat.cast_sum, Nat.cast_le] at he
  exact he

lemma negated_regular {w : ℕ → ℝ} (h : T.Grants B w) (i : Node) : B.Regular (T.region i) (T.negated i) :=
  regular_smul _ (products_regular T B h i)

lemma negated_bound {w : ℕ → ℝ} (h : T.Grants B w) (i : Node) :
    B.supBounds (T.center i) (T.region i) (T.negated i) (T.basePrice B w i) := by
  rw [← T.basePrice_eq B]
  by_cases hi : Ursell.coefficient T.graph i.2=0
  · simp only [negated,constant,hi,neg_zero,zero_div,Complex.ofReal_zero,zero_smul,norm_zero,zero_mul]
    exact norm_zero (E:=ℂ) ▸ bound_const _
  refine bound_smul _ (product_bound Finset.univ (T.cast ∘ i.2) (w ∘ i.2) (T.support ∘ i.2)
    (T.anchor ∘ i.2) (fun j _ => T.region_has i j) (fun j _ => T.region_has _ _ (T.address _).anchor) (T.anchored i)
      (covers T B i hi) ?_ (fun j _ => (h _).1) (fun j _ => (h _).2))
  change Finset.univ.card ≤ ∑ j,coverNumber B.B (T.support (i.2 j))
  have hc := Finset.sum_le_sum (f:=fun _ => 1) (s:=Finset.univ) (
    fun j _ => (Animals.price_pos B.B (T.support (i.2 j))).mpr ⟨_,(T.address _).anchor⟩)
  rw [Finset.sum_const, smul_eq_mul,mul_one] at hc
  exact hc

def rate (B : BudgetPoint) (γ q : ℝ) := distanceCost B * ((deg B).factorial * Real.exp 1) * (γ*(1-q)⁻¹)

lemma fee_hit {w : ℕ → ℝ} {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Trees.Ready T.support B.B w (a+2) γ δ q) :
    Ac.Hit T.region B.B (T.basePrice B w) a (rate B γ q) := by
  let z (_ : ℕ) : ℝ := 0
  have ht : Reserves.tariff w z z 1=w := by ext; simp [Reserves.tariff,z]
  have he' : 2*(1:ℝ)=2 := by norm_num
  rw [← ht,← he'] at h
  intro x
  have hh := Reserves.cluster_prices T.support B.B w z z T.graph T.test (by rw [ht] at h; exact h.2.2.2.2.1) (fun _ => le_rfl)
    (T:=0) (U:=0) zero_lt_one ha h 0 (deg B) x (fun _ => True) (fun s _ _ _ _ => ⟨Finset.sum_nonneg (fun j _ =>
      show (0:ℝ) ≤ ↑(coverNumber B.B (T.support (s.2 j)))+0 from by positivity),by simp [z]⟩)
  convert budget_scale (zero_le_one.trans (distanceCost_pos (B:=B))) hh using 1
  · funext i
    simp only [true_and, Nat.zero_le,↓reduceIte]
    by_cases he : x ∈ T.region i
    · change (if x∈T.region i then _ else _) = distanceCost B * ((if x∈T.region i then _ else _) * _)
      rw [if_pos he,if_pos he]; simp only [basePrice,productFee,Reserves.clusterPrice,load,z,Reserves.weight,add_zero,
        Trees.currency,region,Nat.cast_sum]; ring
    change (if x∈T.region i then _ else _) = distanceCost B * ((if x∈T.region i then _ else _) * _)
    rw [if_neg he,if_neg he,zero_mul,mul_zero]
  simp [rate,Reserves.extract,Reserves.polyPrice,Reserves.treeYield,mul_assoc]

lemma base_pos {w : ℕ → ℝ} (hw : ∀ i,0≤w i) (i : Node) : 0 ≤ T.basePrice B w i :=
  mul_nonneg (zero_le_one.trans (productFee_pos _)) (Ursell.clusters_nonneg T.graph hw _)

lemma fee_one {w : ℕ → ℝ} {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Trees.Ready T.support B.B w (a+2) γ δ q)
    (hr : rate B γ q ≤ 1) (i : Node) : T.basePrice B w i ≤ 1 := by
  have he := budget_single (T.fee_hit B ha h (T.center i)) i
  rw [if_pos (T.anchored i)] at he
  exact (le_mul_of_one_le_right (T.base_pos B h.2.2.2.2.1 _) (Real.one_le_exp (by positivity))).trans (he.trans hr)

def fee (w : ℕ → ℝ) (i : Node) := mayerCost B.order * T.basePrice B w i

/-- Realizable bill for all exponential factors, uniform-in-volume hit with actual union cover.
The `+2` logarithm reserve here is in addition to `δ` in `Ready`. -/
lemma budget {w : ℕ → ℝ} {a γ δ q : ℝ} (ha : 0 ≤ a) (h : Trees.Ready T.support B.B w (a+2) γ δ q)
    (hg : T.Grants B w) (hr : rate B γ q ≤ 1) :
    (∀ i, B.Regular (T.region i) (T.expTerm i) ∧ B.supBounds (T.center i) (T.region i) (T.expTerm i) (T.fee B w i)) ∧
      Ac.Hit T.region B.B (T.fee B w) a (mayerCost B.order * rate B γ q) := by
  refine ⟨fun i => ⟨mayer_regular (T.negated_regular B hg i),mayer_bound (T.negated_regular B hg i)
    (T.negated_bound B hg i) (fee_one T B ha h hr i)⟩,fun x => ?_⟩
  convert budget_scale (by linarith [mayerCost_three_le B.order] : 0 ≤ mayerCost B.order) (T.fee_hit B ha h x) using 1
  funext i; unfold fee; split <;> ring
end Bulk
end YM.Planned.Forced
