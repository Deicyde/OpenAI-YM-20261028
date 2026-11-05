import YM.Extra.SOURCE_HISTORIES.Sizes
import YM.Work.B04

/-!
Linearize exactly the gas part of eq:Jma. `coat R i b`
is the multiplier of the coefficient at address i INSIDE b. Dress with
all compatible histories, using one unchanged admissibility/flag alphabet
and vacuum coefficients. Absolute proofs use the *actual* cap (even
though some bounds in this interchange are only finite volume).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories

open Lattice Wilson RG Source Labels Function Set Filter MeasureTheory
open scoped BigOperators Topology Matrix.Norms.Frobenius

variable {n : Side} {G : Gauge} {d : ℕ} {F : Labels.Frame G d} {R : Rep G n} {σ C Λ δ w : ℝ}

open scoped Classical in
def coat (R : Rep G n) (i : ℕ) (b : Finset ℕ) (U : Config G n) : ℂ :=
  if i ∈ b ∧ R.activities.admissible R.p U b then
    ∏ j ∈ b.erase i, (R.activities.K j U : ℂ)
  else 0

def dressed (R : Rep G n) (i : ℕ) (U : Config G n) := ∑' b, coat R i b U

lemma coat_budget (h : R.Lawful σ C Λ δ w) : ∃ c : ℝ, 0 ≤ c ∧
    ∃ p : ℕ → Finset ℕ → ℝ, (∀ i, SumBudget (p i) c) ∧ ∀ i b U, ‖coat R i b U‖ ≤ p i b := by
  classical
  obtain ⟨a,ha,ha'⟩ := Activities.K_total h.labels.boundK
  let z : Finset ℕ → ℝ := fun b => ∏ j ∈ b, a j
  have hz b : 0 ≤ z b := Finset.prod_nonneg fun i _ => (ha' i).1
  have hs : Summable z := summable_finsetProd_of_summable_nonneg (fun i => (ha' i).1) ha
  let q (i : ℕ) (b : Finset ℕ) := if i ∈ b then z (b.erase i) else 0
  refine ⟨(∑' b, z b),tsum_nonneg hz,q,fun i => ?_,fun i b U => ?_⟩
  · have hp (b) : 0 ≤ q i b := by unfold q; split; exact hz _; exact le_rfl
    have he : ∀ D : Finset (Finset ℕ), ∑ b ∈ D, q i b ≤ ∑' b, z b := by
      intro D
      let T := D.filter fun b => i ∈ b
      have hx : ∀ a ∈ T, i ∈ a := fun a ha => (Finset.mem_filter.mp ha).2
      calc
        ∑ b ∈ D, q i b = ∑ b ∈ T, z (b.erase i) := by rw [show T=D.filter _ from rfl, Finset.sum_filter]
        _ = ∑ b ∈ T.image (fun b => b.erase i), z b := by
          rw [Finset.sum_image]; intro a ha b hb he; simpa only [Finset.insert_erase (hx a ha), Finset.insert_erase (hx b hb)] using congr_arg (insert i) he
        _ ≤ ∑' b, z b := hs.sum_le_tsum _ (fun b _ => hz b)
    exact ⟨hp,summable_of_sum_le hp he,Real.tsum_le_of_sum_le hp he⟩
  unfold coat
  split <;> rename_i hh
  · unfold q; rw [if_pos hh.1,norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => (Complex.norm_real _).trans_le ((ha' i).2 U))
  · rw [norm_zero]
    unfold q; split; exact hz _; exact le_rfl

lemma coat_meas (h : R.Lawful σ C Λ δ w) (i : ℕ) (b : Finset ℕ) : Measurable (coat R i b) := by
  classical
  by_cases hi : i ∈ b
  · unfold coat; simp only [hi,true_and]
    refine Measurable.ite (R.activities.admissible_borel ..) (Finset.measurable_fun_prod _ fun i _ =>
      Complex.continuous_ofReal.measurable.comp (h.labels.forced.meas i)) measurable_const
  unfold coat; simp only [hi,false_and,if_false]; exact measurable_const

lemma dressed_meas (h : R.Lawful σ C Λ δ w) (i : ℕ) : Measurable (dressed R i) :=
  Measurable.tsum (coat_meas h i)

lemma dressed_budget (h : R.Lawful σ C Λ δ w) : ∃ c : ℝ, 0 ≤ c ∧
    (∀ i, Dominated (coat R i)) ∧ ∀ i U, ‖dressed R i U‖ ≤ c := by
  obtain ⟨c,hc,p,hp,hq⟩ := coat_budget h
  have hu (i) : Dominated (coat R i) := ⟨p i,(hp i).2.1,hq i⟩
  refine ⟨c,hc,hu,fun i U => (norm_tsum_le_tsum_norm ?_).trans ?_⟩
  · exact (hu i).absolute U
  exact (Summable.tsum_le_tsum (fun b => hq i b U) ((hu i).absolute U) ((hp i).2.1)).trans (hp i).2.2

lemma marked_as (P : Coefficient F n) (R : Rep G n) (b) (U) :
    P.marked R b U = ∑' i, P.forced i U * coat R i b U := by
  classical
  rw [tsum_eq_sum (s:=b)]
  · unfold Coefficient.marked
    split <;> rename_i ha
    · exact Finset.sum_congr rfl fun i hi => by simp [coat,hi,ha]
    simp [coat,ha]
  intro i hi
  simp [coat,hi]

/-- Absolute bid on all individual history uses even before erasing the
pair-index order. -/
lemma coat_all (h : R.Lawful σ C Λ δ w) {y : ℕ → Config G n → ℂ} (ha : Dominated y) :
    Dominated (fun p : ℕ × Finset ℕ => fun U => y p.1 U * coat R p.1 p.2 U) := by
  obtain ⟨c,-,p,hp,hq⟩ := coat_budget h
  obtain ⟨a,hs,ht⟩ := ha
  have hu i : 0 ≤ a i := (norm_nonneg _).trans (ht i 1)
  have he i := budget_scale (hp i) (hu i)
  refine ⟨(fun x => a x.1*p x.1 x.2), (budget_prod (f := fun x => a x.1*p x.1 x.2) he (hs.mul_right c)).2.1, fun x U => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (ht ..) (hq ..) (norm_nonneg _) (hu _)

lemma rem_dominated {P : Coefficient F n} {o : Site n} {u v : ℝ} (p : P.remBound o R u v) : Dominated P.forced := by
  obtain ⟨a,b,-,-,-,-,-,e,he,hh⟩ := p
  exact ⟨_,he.2.1,fun i U => ((hh i).2 U).trans (R.p.loMass _ _ (hh i).1)⟩

theorem dress_eq (h : R.Lawful σ C Λ δ w) {P : Coefficient F n} (ha : Dominated P.forced) (U) :
    ∑' b, P.marked R b U = ∑' i, P.forced i U * dressed R i U := by
  simp_rw [marked_as, dressed, ← tsum_mul_left]
  exact Summable.tsum_comm ((coat_all h ha).summable U)

lemma dress_abs (h : R.Lawful σ C Λ δ w) {y : ℕ → Config G n → ℂ} (ha : Dominated y) :
    Dominated (fun i U => y i U * dressed R i U) := by
  obtain ⟨p,-,-,hp⟩ := dressed_budget h
  obtain ⟨a,hs,ht⟩ := ha
  refine ⟨_,hs.mul_right p,fun i U => ?_⟩
  rw [norm_mul]; exact mul_le_mul (ht i U) (hp i U) (norm_nonneg _) ((norm_nonneg _).trans (ht i U))

end YM.Extra.Histories
