import YM.Next.MULTISOURCE.Moist

/-! support roots and price at one coefficient. Prices let ZERO budgets travel. -/

set_option autoImplicit false
noncomputable section
namespace YM.Multi.Desk
open RG Wilson Lattice Finset Filter MeasureTheory Marker MvPolynomial
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {n : Side} {G : Gauge} {I : Type*} [Fintype I] [DecidableEq I]
variable {P : Rep G n} (T : Reservoir P I) {κ : ℝ} {K : Set (I → ℂ)} (H : T.Tested κ K)

def bite (q : Grade I) (i : ℕ) := fun x => coeff q (T.D i x)
def chew (q : Grade I) (i : ℕ) := fun x => coeff q (T.K i x)
def mints (q : Grade I) (i : ℕ) := sInf (taps P.p (T.support i) (bite T q i))
def tolls (q : Grade I) (i : ℕ) := sInf (boxp (chew T q i))

def dome (r : I→ℝ) : Set (I→ℂ) := {z | ∀ i, ‖z i‖ ≤ r i}

include H

section
variable (q : Grade I) (Z : Finset ℕ) (r : I→ℝ) (hr : ∀ i, 0 ≤ r i) (hh : 0 < price r q) (he : dome r ⊆ K)

include hr hh he
lemma egress :
    (∀ i∈Z,P.p.Regular (T.support i) (bite T q i) ∧ mints T q i∈taps P.p (T.support i) (bite T q i)) ∧
      ∀ x : Site n, (∑ i∈ Z,if x∈T.support i then burn P.p 2 (T.support i)*mints T q i else 0) ≤ (price r q)⁻¹ := by
  obtain ⟨N,hN,hq,HN⟩ := span (Z.biUnion fun i => (H.polya i).choose) q
  have hp t : looped r N t ∈ K := he (show looped r N t ∈ dome r from fun i => (circle_val r N t hr hN i).le)
  choose b hb hB using fun t => H.bulk (looped r N t) (hp t)
  have hg (i) (hi : i∈Z) : P.p.Regular (T.support i) (bite T q i) ∧ (∑ t,‖load r N t q‖* b t i) ∈ taps P.p (T.support i) (bite T q i) :=
    tariffH _ _ _ _ r hq hh hN (fun x p hv => HN _ (mem_biUnion.mpr ⟨i,hi,(H.polya i).choose_spec _ hv⟩))
      _ (fun t => ⟨H.smooth _ (hp t) _,hb t i⟩)
  refine ⟨fun i hi => ⟨(hg _ hi).1,has_tap ⟨_,(hg i hi).2⟩⟩,fun x => ?_⟩
  have hU (i) (hi : i∈Z) : (if x∈T.support i then burn P.p 2 (T.support i)*mints T q i else 0) ≤
      ∑ t : Cir I N, ‖load r N t q‖ * (if x∈T.support i then burn P.p 2 (T.support i)*b t i else 0) := by
    by_cases hx : x∈T.support i
    · simp only [hx, if_true]; simp_rw [mul_left_comm ‖_‖, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (tap_le (hg _ hi).2) (burn_pos ..).le
    simp only [hx, if_false,mul_zero, sum_const_zero,le_refl]
  apply (sum_le_sum hU).trans
  rw [sum_comm,← total r q hh hN]; apply sum_le_sum; intro i _; rw [← mul_sum]
  exact mul_le_of_le_one_right (norm_nonneg _) (((hB i x).2.1.sum_le_tsum Z (fun j _ => (hB i x).1 j)).trans (hB i x).2.2)

lemma vents :
    (∀ i∈Z,Legible P.p (T.k i) (chew T q i) ∧ tolls T q i∈boxp (chew T q i)) ∧
      ∀ x : Site n, (∑ i∈ Z,if x∈(T.k i).zone then burn P.p 2 (T.k i).zone*tolls T q i else 0) ≤ κ * (price r q)⁻¹ := by
  obtain ⟨N,hN,hq,HN⟩ := span (Z.biUnion fun i => (H.polyb i).choose) q
  have hp t : looped r N t ∈ K := he (show looped r N t ∈ dome r from fun i => (circle_val r N t hr hN i).le)
  choose b hb hB using fun t => H.titles (looped r N t) (hp t)
  have hg (i) (hi : i∈Z) : Legible P.p (T.k i) (chew T q i) ∧ (∑ t,‖load r N t q‖* b t i) ∈ boxp (chew T q i) :=
    tariffK _ _ _ _ r hq hh hN (fun x p hv => HN _ (mem_biUnion.mpr ⟨i,hi,(H.polyb i).choose_spec _ hv⟩))
      _ (fun t => ⟨H.reads _ (hp t) _,hb t i⟩)
  refine ⟨fun i hi => ⟨(hg _ hi).1,has_box ⟨_,(hg i hi).2⟩⟩,fun x => ?_⟩
  have hU (i) (hi : i∈Z) : (if x∈(T.k i).zone then burn P.p 2 (T.k i).zone*tolls T q i else 0) ≤
      ∑ t : Cir I N, ‖load r N t q‖ * (if x∈(T.k i).zone then burn P.p 2 (T.k i).zone*b t i else 0) := by
    by_cases hx : x∈(T.k i).zone
    · simp only [hx, if_true]; simp_rw [mul_left_comm ‖_‖, ← mul_sum]
      exact mul_le_mul_of_nonneg_left (box_le (hg _ hi).2) (burn_pos ..).le
    simp only [hx, if_false,mul_zero,sum_const_zero,le_refl]
  apply (sum_le_sum hU).trans
  rw [sum_comm,← total r q hh hN,mul_comm κ, sum_mul]; apply sum_le_sum; intro i _; rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (((hB i x).2.1.sum_le_tsum Z (fun j _ => (hB i x).1 j)).trans (hB i x).2.2) (norm_nonneg _)
end
end YM.Multi.Desk
