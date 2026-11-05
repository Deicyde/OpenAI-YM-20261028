import YM.Extra.WILSON_STARTUP.Cake

/-!
# Actual fused startup dictionary: forcing width and spare addresses

Width assertion is intentionally a theorem on all nonzero receipts, NOT a
vacuous geometry assertion derived from addresses of the nonzero vacuum
terms alone when handling the moves/marks. For arbitrary footprint/inventory
pairs, infinitely many dormant K labels with exact predicates. Similar
E labels. No changing the dictionary once the curve is fitted.
-/
noncomputable section
set_option autoImplicit false
namespace YM.WilsonStartup
open Lattice RG Wilson Start Padded Ac Ovens Ovens.Pipes
open scoped Classical Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side} (c : Clip) (b : BudgetPoint) (β : ℝ)

-- source propagation, can reuse condition on other protocols
structure Wide (R : Rep G n) : Prop where
  footprints i : ∀ U, R.activities.K i U ≠ 0 → region R.p (R.activities.forced i).inventory ⊆ (R.activities.forced i).support

namespace Start

theorem wide : Wide (presentation G n c b β) := by
  constructor
  intro i U h z hz
  let e := enumeration G n
  let q := (dictionary G n)
  let w := payload c b G n β
  change z ∈ q.skin (e i).val
  change z ∈ region b (q.plot (e i).val) at hz
  obtain ⟨a,ha,hz⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp ha
  have hJ : Sum.inl j ∈ (e i).val := Finset.mem_toLeft.mp hj
  change solid e b w i U ≠ 0 at h
  unfold solid at h; split at h
  · have hL := admitted_actual (G:=G) (b:=b) (c:=c) (β:=β) (i:=j) (U:=U) ((Finset.prod_ne_zero_iff.mp h) _ hJ)
    refine Finset.mem_biUnion.mpr ⟨_,hJ,?_⟩
    change z ∈ extent n j; rw [show extent n j = _ from hL.2.2]
    exact Finset.mem_biUnion.mpr ⟨a,he,hz⟩
  exact (h rfl).elim

lemma singleton_contains (j : ℕ) : (dictionary G n).contains {Sum.inl j} := by
  simp only [Pipes.contains,lefts]; refine ⟨⟨j, by simp⟩,⟨Finset.singleton_nonempty _,?_⟩,?_⟩
  · simp only [Finset.mem_singleton]; rintro i rfl k rfl; exact .refl
  simp [Set.Pairwise]

def single (G : Gauge) (n : Side) (j : ℕ) := (enumeration G n).symm ⟨{Sum.inl j},singleton_contains j⟩



abbrev nth {α : Type*} [Countable α] [Nonempty α] (a : α) (i : ℕ) : ℕ := (codec α).symm (a,i+1)
@[simp] theorem nth_name {α : Type*} [Countable α] [Nonempty α] (a : α) (i : ℕ) : name α (nth a i) = a := by simp [name,nth]
@[simp] theorem nth_not_fixed {α : Type*} [Countable α] [Nonempty α] (a : α) (i : ℕ) : ¬fixed α (nth a i) := by simp [fixed,nth]

def reserveE (q : Blank n) (j : ℕ) := nth (Sum.inr q : Sheet n) j

def reserveK (G : Gauge) (q : Foot n) (j : ℕ) := single G n (nth q j)










end Start
end YM.WilsonStartup
