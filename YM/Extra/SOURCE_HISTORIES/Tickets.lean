import YM.Extra.SOURCE_HISTORIES.Clusters
import YM.Extra.SOURCE_HISTORIES.Drift

/-!
# Labels and prices of a translated column

Use actual vacuum-provided label permutations (path.Selected required when
assuming translation of exponent). Tests/exclusions/read halos preserved.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Histories.Drift
open Function Filter MeasureTheory Set Lattice Wilson RG Source Labels Bid Motion
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {n : Side} {d : ℕ} {F : Labels.Frame G d}
variable (t : Site n) {R : Rep G n} (H : R.activities.Moves 1 t)

lemma move_support (i) : (R.activities.forced (H.kp i)).support=relocated t (R.activities.forced i).support := by
  rw [H.forced_support,aff,relocated]
lemma move_inventory (i) : (R.activities.forced (H.kp i)).inventory=relocated t (R.activities.forced i).inventory := by
  rw [H.forced_inventory,aff,relocated]

lemma move_K (i) (U) : R.activities.K (H.kp i) U=R.activities.K i (translate t U) := by
  rw [H.valuesK,pull_one]

def ticket := H.kp.finsetCongr
lemma ticket_image (x : Finset ℕ) : ticket t H x=x.image H.kp := by simp [ticket,Finset.map_eq_image]
lemma ticket_mem (x : Finset ℕ) (i : ℕ) : i∈x ↔ H.kp i∈ ticket t H x := by rw [ticket_image]; simp


lemma seats (b : Finset ℕ) (U : Config G n) : R.activities.admissible R.p U (ticket t H b) ↔
    R.activities.admissible R.p (translate t U) b := by
  let X := fun i => (R.activities.forced i).support
  let I := fun i => (R.activities.forced i).inventory
  have he i j : Disjoint (X (H.kp i)) (X (H.kp j)) ↔ Disjoint (X i) (X j) := by
    unfold X; rw [move_support,move_support]; exact Finset.disjoint_image (add_left_injective t)
  have hh : (ticket t H b).biUnion I = relocated t (b.biUnion I) := by
    rw [ticket_image,Finset.image_biUnion,relocated,Finset.biUnion_image]
    simp only [I, move_inventory, relocated]
  change (_ ∧ (ticket t H b).biUnion I=flags R.p.threshold U) ↔ _
  rw [hh,← flag t U, relocated, relocated, (Finset.image_injective (add_left_injective t)).eq_iff]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨fun i hI j hJ hK => (he i j).mp (ha ((ticket_mem ..).1 hI) ((ticket_mem ..).1 hJ) (H.kp.injective.ne hK)),hb⟩
  rintro ⟨ha,hb⟩
  refine ⟨?_,hb⟩
  intro i hi j hj hk
  obtain ⟨i,rfl⟩ := H.kp.surjective i; obtain ⟨j,rfl⟩ := H.kp.surjective j
  exact (he i j).mpr (ha ((ticket_mem ..).2 hi) ((ticket_mem ..).2 hj) (H.kp.injective.ne_iff.mp hk))



include H in
lemma gases (U : Config G n) : R.activities.gas R.p U=R.activities.gas R.p (translate t U) := by
  have ht b : R.activities.gasOccurrence R.p (ticket t H b) U= R.activities.gasOccurrence R.p b (translate t U) := by
    unfold Activities.gasOccurrence
    rw [seats,ticket_image,Finset.prod_image H.kp.injective.injOn]; simp only [move_K]
  unfold Activities.gas; rw [← (ticket t H).tsum_eq (fun b => R.activities.gasOccurrence R.p b U)]
  exact tsum_congr ht

def stamp (P : Coefficient F n) : Coefficient F n where
  x := P.x
  support i := relocated t (P.support i)
  regular i := P.regular i ∘ translate t
  forced i := P.forced (H.kp.symm i) ∘ translate t






end YM.Extra.Histories.Drift
