import YM.Extra.ITERATION_NO_LOSS.TermNorm
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Polynomial
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Sweep.Funds
import YM.SectorNext.RECONNECTED_LOCALITY.Gaussian


/-!
# Sparse sweep

From actual costs and comparison on every at-most-K sub-read (K
fixed, with room for all powers of one monomial and one trigger), on the
SAME cloud pair. To full local tests of bounded degree whose number of
coordinates and path terms and support as a whole can grow. Each term
pulled exactly from the same reads; don't assert factor independence for
monomials or choose new gauge/log data after the polynomial.
-/

set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
open Function Filter Set Finset MeasureTheory MvPolynomial
open Next.SectorChange.Gaussian
open Primitives.GCC.LocalPolynomial (Script)
open scoped Topology BigOperators Classical

variable {α β I : Type} [MeasurableSpace α] [MeasurableSpace β] [Fintype I]
variable {K D : ℕ} {E x : ℝ}

/-- Local subread of same normalized comparison. -/
def crop (s : Finset I) (Y : α → Vec I) (z : α) : Vec (↥s) := Y z ∘ Subtype.val

/-- NormalBill of K,D common. Does not require K to pay all of I. -/
structure Sections (K D : ℕ) (E : ℝ) (μ : Measure α) (Y : α → Vec I) : Prop where
  measured : Measurable Y
  available (s : Finset I) (hs : s.card ≤ K) (p : Script (↥s)) (hp : p.totalDegree ≤ D) :
    Costed K E (coefficientNorm p * normalBill K E D) μ (crop s Y) (peval p ∘ crop s Y)

section restrict

abbrev mono (w : I→₀ℕ) : Script I := (monomial w) 1
abbrev localIndex (w : I→₀ℕ) (s : Finset I) : (↥s) →₀ ℕ := w.subtypeDomain (· ∈ s)

omit [Fintype I] in
lemma mono_degree (w : I→₀ℕ) : (mono w).totalDegree = w.sum (fun _ j => j) :=
  totalDegree_monomial w one_ne_zero

omit [Fintype I] in
lemma mono_slots (w : I→₀ℕ) : w.support.card ≤ (mono w).totalDegree := by
  rw [mono_degree,Finsupp.sum]
  calc
    _ = ∑ _i∈w.support,1 := by simp
    _ ≤ _ := sum_le_sum fun _ hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)

lemma mono_degree_sub (w : I→₀ℕ) (s : Finset I) (hs : w.support ⊆ s) :
    (mono (I:=↥s) (localIndex w s)).totalDegree = (mono w).totalDegree := by
  rw [mono_degree, Finsupp.sum_fintype _ _ (fun _ => rfl),mono_degree,Finsupp.sum_fintype w _ (fun _ => rfl)]
  simp only [localIndex, Finsupp.subtypeDomain_apply]
  rw [← Finset.sum_subtype s (fun _ => Iff.rfl) (fun i => w i)]
  exact Finset.sum_subset (subset_univ s) (fun i _ hi => not_ne_iff.mp (fun hx => hi (hs (Finsupp.mem_support_iff.mpr hx))))

lemma mono_sub (w : I→₀ℕ) (s : Finset I) (hs : w.support ⊆ s) (z : Vec I) :
    peval (mono w) z = peval (mono (localIndex w s)) (z ∘ Subtype.val) := by
  unfold peval mono; rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => by simp),
    Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [localIndex, Finsupp.subtypeDomain_apply, Function.comp_apply]; congr 1
  rw [← Finset.prod_subtype s (fun _ => Iff.rfl) (fun i => (z i:ℂ)^w i)]
  symm; apply Finset.prod_subset (subset_univ s)
  intro i _ hi; rw [show w i=0 from not_ne_iff.mp (fun hx => hi (hs (Finsupp.mem_support_iff.mpr hx))),pow_zero]

lemma peval_dist (p : Script I) (z : Vec I) : peval p z = ∑ i∈p.support,coeff i p * peval (mono i) z := by
  unfold peval mono; nth_rw 1 [as_sum p]; simp_rw [map_sum, aeval_monomial]; simp

variable {μ : Measure α} {Y : α → Vec I}
lemma Sections.region (h : Sections K D E μ Y) (w : I →₀ ℕ) (hw : (mono w).totalDegree ≤ D)
    (s : Finset I) (he : w.support ⊆ s) (hs : s.card ≤ K) :
    Costed K E (normalBill K E D) μ (crop s Y) (peval (mono w) ∘ Y) := by
  have ht := h.available s hs (mono (localIndex w s)) ((mono_degree_sub w s he).le.trans hw)
  rw [show peval (mono w) ∘ Y = peval (mono (localIndex w s)) ∘ crop s Y from funext fun z => mono_sub w s he (Y z)]
  rw [show coefficientNorm _=1 from coefficient_monomial _,one_mul] at ht; exact ht



omit [MeasurableSpace α] in
lemma pieces (Y : α → Vec I) (p : Script I) : peval p ∘ Y = fun z => ∑ i∈p.support,coeff i p*((peval (mono i) ∘ Y) z) :=
    funext fun z => peval_dist p (Y z)


end restrict

/-- Export one callable service for this *pair*. No implication that general
weighted TV can pass to all these coordinates at these prices. -/
structure Collected (K D : ℕ) (E x : ℝ) (μ : Measure α) (ν : Measure β) (Y : α → Vec I) (Z : β → Vec I) : Prop where
  hi : 1 ≤ E
  high : 1 ≤ x
  source (p : Script I) (hp : p.totalDegree ≤ D) : Savings K E (coefficientNorm p*normalBill K E D) μ Y (peval p ∘ Y)
  reference (p : Script I) (hp : p.totalDegree ≤ D) : Savings K E (coefficientNorm p*normalBill K E D) ν Z (peval p ∘ Z)
  compare (p : Script I) (hp : p.totalDegree ≤ D) :
    ‖(∫ z,peval p (Y z) ∂μ)-(∫ z,peval p (Z z) ∂ν)‖ ≤ coefficientNorm p * normalError K E D x


end YM.PhysicalNext.WeightedGaussianMarginal45C.Sweep
