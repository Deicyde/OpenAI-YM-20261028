import YM.Next.RANK.Value


/-!
# Actual push for comparison computations (can restart)

Fix `(N,p,k)` with k the depth/level of k-grid insertions. No averaging over a
trajectory. From N down through k the kernels are exactly from the physical
history, including coupling, tags and choices. Below k this ancillary computation
may use different numerical couplings in the same block method : still
one sequence of kernels, and pushes of the entire already-coupled density. This
never changes the physical Wilson law or the history delivered in end theorems.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank
open Lattice Wilson RG MeasureTheory Filter Set Function
open scoped Topology Matrix.Norms.Frobenius

variable {G : Gauge}

structure Course (C : Family G) (N p k : ℕ) where
  changeβ : ℕ → ℝ
  allow : k ≤ N
  same (i) : k ≤ i → i≤N → changeβ i=C.path.β N p i
  pos (i) : i≤N → 0 < changeβ i

namespace Course
variable {C : Family G} {N p k : ℕ} (X : Course C N p k)

section
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (F : Config G (C.side N p) → W)

def flow (m) (hm : m ≤ N) : Config G (C.side m p) → W :=
    Nat.decreasingInduction (motive:=fun m _ => Config G (C.side m p) → W) (fun i _ f =>
      (C.path.levels.clock.op i p).push (X.changeβ (i+1)) f) F hm

lemma flow_self : X.flow F N le_rfl=F := Nat.decreasingInduction_self ..
lemma flow_step (m) (hm : m<N) : X.flow F m hm.le=(C.path.levels.clock.op m p).push (X.changeβ (m+1)) (X.flow F (m+1) hm) :=
    Nat.decreasingInduction_succ_left ..

lemma flow_int (h : Integrable F (prior G (C.side N p))) (m) (hm : m ≤ N) : Integrable (X.flow F m hm) (prior G (C.side m p)) := by
  induction hm using Nat.decreasingInduction with
  | self => rw [flow_self]; exact h
  | of_succ i hi ih => rw [X.flow_step F i hi]; exact StepData.push_integrable (C.path.levels.transition_mass ..) _ ih

variable [CompleteSpace W]

lemma flow_sum (h : Integrable F (prior G (C.side N p))) (m) (hm : m ≤ N) :
    (∫ U, X.flow F m hm U ∂prior G _) = ∫ U,F U ∂prior G _ := by
  induction hm using Nat.decreasingInduction with
  | self => rw [flow_self]
  | of_succ i hi ih => rw [X.flow_step F i hi, StepData.push_integral (C.path.levels.transition_mass ..) _ (X.flow_int _ h (i+1) hi), ih]

lemma flow_linear {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : W →L[ℝ] Y) (h : Integrable F (prior G (C.side N p))) (m) (hm : m ≤ N) : L ∘ X.flow F m hm = X.flow (L ∘ F) m hm := by
  induction hm using Nat.decreasingInduction with
  | self => rw [flow_self,flow_self]
  | of_succ i hi ih =>
    rw [X.flow_step F i hi,X.flow_step _ i hi,← ih]; funext x
    simp only [Function.comp_apply,StepData.push]
    rw [← L.integral_comp_comm (StepData.push_slice (C.path.levels.transition_mass ..) x _ (X.flow_int F h (i+1) hi))]
    simp only [L.map_smul]
end

def vacuum (m : ℕ) (hm : m≤N) : Config G (C.side m p) → ℝ := X.flow (bare (C.beta N p)) m hm


lemma vacuum_total {m : ℕ} (h : m ≤ N) : (∫ U,X.vacuum m h U∂prior G (C.side m p))=Wilson.partition G (C.side N p) (C.beta N p) := X.flow_sum _ (bare_integrable _) _ h

lemma vacuum_lower {m : ℕ} (h : m ≤ N) : ∀ U : Config G (C.side m p), 0 ≤ X.vacuum m h U := by
  unfold vacuum; induction h using Nat.decreasingInduction with
  | self => intro U; rw [flow_self]; exact (bare_pos ..).le
  | of_succ i hi ih => rw [X.flow_step _ i hi]; exact fun U => integral_nonneg fun u => mul_nonneg (StepData.density_positive ..) (ih _)

/-- Above and including k the *actual* denotational density agrees pointwise. -/
lemma vacuum_at (h : C.Makes) (m : ℕ) (hm : m ≤ N) (hk : k≤m) : X.vacuum m hm=(C.path.rep N p m).eval := by
  unfold vacuum
  induction hm using Nat.decreasingInduction with
  | self => rw [flow_self]; exact (h.wilson.starts N p).2.symm
  | of_succ i hi ih => rw [X.flow_step _ i hi, X.same (i+1) (hk.trans (Nat.le_succ _)) hi,ih (hk.trans (Nat.le_succ _))]; exact (h.wilson.steps N p i hi).1.symm

/-- Tie witness for reused denominator. Even if found by alternative local
estimates, this is always integrable and no scalar ambiguity left. -/
structure Uses (m : ℕ) (hm : m≤N) (P : Rep G (C.side m p)) : Prop where
  density : X.vacuum m hm=P.eval
  coupling : X.changeβ m=P.beta

end Course
end YM.Next.Rank
