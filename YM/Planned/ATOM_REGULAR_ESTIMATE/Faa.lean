import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Bid.Fuels
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Pressure.Seeds
import YM.Work.A05.Read
import YM.Work.A07
import YM.Work.B04
import YM.Work.B06

/-!
Finite (`C^k` at a point) chain and product costs for passage under the
component integral. Orders in this module are not formal truncation orders
of an analytic slot. `F` may have only the source order. All jets in
`iteratedFDeriv` normalization (no /k!).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular
open Function Filter
open scoped Topology BigOperators ContDiff

def patterns (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (Fintype.card (OrderedFinpartition j):ℝ)
lemma card_le_patterns {i n : ℕ} (hi : i ≤ n) : (Fintype.card (OrderedFinpartition i):ℝ) ≤ patterns n :=
  Finset.single_le_sum (fun j _ => Nat.cast_nonneg (Fintype.card (OrderedFinpartition j))) (Finset.mem_range.mpr (by omega))
lemma patterns_nonneg (n : ℕ) : 0 ≤ patterns n := by unfold patterns; positivity

variable {E F Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {U : E → F} {G : F → Z}
  {x : E} {k n : ℕ} {C D : ℝ}

/-- Version with tests on the true sensitivities, e.g. when there is a
Taylor cancellation in the outer factor on those particular arguments. -/
theorem slots_bound (hu : ContDiffAt ℝ n U x) (hf : ContDiffAt ℝ n G (U x)) (hk : k ≤ n) (hC : 0 ≤ C)
    (h : ∀ (q : OrderedFinpartition k) (w : Fin k → E), (∀ i, ‖w i‖ ≤ 1) →
      ‖(iteratedFDeriv ℝ q.length G (U x)) (fun i =>
        iteratedFDeriv ℝ (q.partSize i) U x (fun j => w (q.emb i j)))‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (G ∘ U) x‖ ≤ patterns n * C := by
  refine op_le_of_unit (mul_nonneg (patterns_nonneg _) hC) (fun v hv => ?_)
  rw [iteratedFDeriv_comp hf hu (Nat.cast_le.mpr hk), FormalMultilinearSeries.taylorComp, sum_apply]
  apply le_trans (norm_sum_le ..) ((Finset.sum_le_sum (fun q _ => ?_)).trans
    (b:=∑ _q : OrderedFinpartition k, C) ?_)
  · simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using!
      mul_le_mul_of_nonneg_right (card_le_patterns hk) hC
  exact h q v hv

/-- Uniform composition price. The inner factor pays ONLY for positive-order
jets (and at least one currency unit). -/
theorem nest_bound (hu : ContDiffAt ℝ n U x) (hf : ContDiffAt ℝ n G (U x)) (hk : k ≤ n)
    (hC : 0 ≤ C) (hD : 1 ≤ D)
    (h : ∀ i, 0 < i → i ≤ n → ‖iteratedFDeriv ℝ i U x‖ ≤ D)
    (hb : ∀ i ≤ n, ‖iteratedFDeriv ℝ i G (U x)‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (G ∘ U) x‖ ≤ patterns n * (C * D^n) := by
  have hp : 0 ≤ D := zero_le_one.trans hD
  refine slots_bound hu hf hk (by positivity) (fun q w hw => ?_)
  let v (i : Fin q.length) := iteratedFDeriv ℝ (q.partSize i) U x (fun j => w (q.emb i j))
  have ht i : ‖v i‖ ≤ D := by
    have hi := h _ (q.partSize_pos i) ((q.partSize_le _).trans hk)
    simpa using ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le hi (fun j => hw (q.emb i j))
  refine le_trans (ContinuousMultilinearMap.le_mul_prod_of_opNorm_le_of_le (hb q.length (q.length_le.trans hk)) ht) ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (q.length_le.trans hk)) hC

/-- Product inside the weighted chart integral. -/
theorem product_bound {f g : E → ℂ} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hc : ∀ i ≤ n, ‖iteratedFDeriv ℝ i f x‖ ≤ C) (hd : ∀ i ≤ n, ‖iteratedFDeriv ℝ i g x‖ ≤ D)
    (hk : k ≤ n) : ‖iteratedFDeriv ℝ k (f * g) x‖ ≤ 2^n * C * D := by
  have hC := (norm_nonneg _).trans (hc 0 (Nat.zero_le _))
  have hD := (norm_nonneg _).trans (hd 0 (Nat.zero_le _))
  have hoo {t : E → ℂ} (h : ContDiffAt ℝ n t x) : ∃ s, IsOpen s ∧ x ∈ s ∧ ContDiffOn ℝ n t s := by
    obtain ⟨u,hu,he⟩ := h.contDiffOn (m:=(n:WithTop ℕ∞)) le_rfl (by simp)
    obtain ⟨s,hs,hy,hx⟩ := _root_.mem_nhds_iff.mp hu
    exact ⟨s,hy,hx,he.mono hs⟩
  obtain ⟨s,hs,hx,h⟩ := hoo hf; obtain ⟨t,ht,hy,h'⟩ := hoo hg
  have hst : UniqueDiffOn ℝ (s ∩ t) := (hs.inter ht).uniqueDiffOn
  have hj : x∈ s ∩ t := ⟨hx,hy⟩
  have hh : (k : WithTop ℕ∞) ≤ n := Nat.cast_le.mpr hk
  change ‖iteratedFDeriv ℝ k (fun y => f y * g y) x‖ ≤ _
  rw [← iteratedFDerivWithin_eq_iteratedFDeriv hst ((hf.mul hg).of_le hh) hj]
  apply le_trans (norm_iteratedFDerivWithin_mul_le (h.mono Set.inter_subset_left) (h'.mono Set.inter_subset_right) hst hj hh) ?_
  calc
    _ ≤ ∑ i ∈ Finset.range (k+1), (k.choose i:ℝ) * C * D := by
      refine Finset.sum_le_sum fun i hi => ?_
      have hx : i ≤ n := by have := Finset.mem_range.mp hi; omega
      have ht : k-i ≤ n := by omega
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hst (hf.of_le (Nat.cast_le.mpr hx)) hj,
        iteratedFDerivWithin_eq_iteratedFDeriv hst (hg.of_le (Nat.cast_le.mpr ht)) hj]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hc i hx) (by positivity)) (hd _ ht) (norm_nonneg _) (by positivity)
    _ = 2^k * C * D := by rw [← Finset.sum_mul,← Finset.sum_mul,← Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow,Nat.cast_ofNat]
    _ ≤ _ := by gcongr; norm_num

end YM.Planned.AtomRegular
