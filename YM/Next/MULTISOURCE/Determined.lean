import YM.Ac.Nodes
import YM.Next.MULTISOURCE.Packs
import YM.Pressure.Rows

/-!
# Translate eval of this whole history
-/
set_option autoImplicit false
noncomputable section

namespace YM.Multi.AxisShift
open RG Lattice Wilson Function Finset MeasureTheory Pack
open scoped Topology Matrix.Norms.Frobenius BigOperators

variable {G : Gauge} {A : Levels G} {p m : ℕ}

lemma commute_tr {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : Site (A.S.side m p)) (β : ℝ) (F : Config G (A.S.side (m+1) p)→X)
    (h : Integrable F (prior G _)) :
    (A.clock.op m p).push β (F ∘ translate ((A.clock.op m p).ratio.embed V))=
      ((A.clock.op m p).push β F) ∘ translate V := by
  funext U; let S := A.clock.op m p; let o := S.ratio.embed V
  let i := fun x : Config G _ => S.density β x (translate V U) • F x
  have he : MeasurePreserving (translate o (K:=G.El)) (prior G _) (prior G _) := by
    rw [show translate o = pull 1 o (K:=G.El) from funext fun U => (pull_one ..).symm]; exact prior_pull _ _
  have hs : Integrable i (prior G _) := StepData.push_slice (A.transition_mass ..) _ F h
  have hg := integral_map (μ:= prior G _) (f:=i) he.aemeasurable
    (show AEStronglyMeasurable i _ from (he.map_eq.symm ▸ hs.aestronglyMeasurable))
  rw [he.map_eq] at hg
  change (∫ x, S.density β x U • F (translate o x) ∂prior G _) = ∫ x,i x ∂prior G _
  rw [hg]; refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have he := (A.blocks m p).symmetric β x U 1 V
  simp only [pull_one] at he
  unfold i; change S.density β x U • _ = S.density β _ _ • _; rw [he]

private theorem positive_kernel {c f : Side} (S : StepData c f) (β : ℝ) (U : Config G f) (V : Config G c)
    (h : S.patch.Branches S.kernel G) : 0 < S.density β U V := by
  classical
  have hp (i : S.Choices) : 0 < S.noise β (S.prediction U i) V :=
    prod_pos fun i _ => mul_pos (inv_pos.mpr (S.penaltyZ_pos β)) (Real.exp_pos _)
  obtain ⟨i,hi⟩ : ∃ i,0 < S.likelihood U i := by
    by_contra! h'
    have he := S.chosen h U
    exact lt_irrefl (0:ℝ) (calc 0 < (1:ℝ) := zero_lt_one
                            _ = _ := he.symm
                            _ ≤ _ := sum_nonpos fun i _ => h' i)
  exact (mul_pos hi (hp i)).trans_le (single_le_sum (a:=i) (f:=fun t =>
    S.likelihood U t*S.noise β (S.prediction U t) V) (fun i _ => mul_nonneg (S.likelihood_pos U i) (hp i).le) (mem_univ i))

variable {H : History G} {N : ℕ}

lemma chosen_positive (h : H.Selected) (hv : m ≤ N) (U : Config G (H.S.side m p)) :
    0 < (H.rep N p m).eval U := by
  induction hv using Nat.decreasingInduction with
  | self => rw [(h.starts ..).2]; exact bare_pos ..
  | of_succ k hk ih =>
    let F (i : Config G (H.S.side (k+1) p)) := (H.levels.clock.op k p).density
      (H.β N p (k+1)) i U • (H.rep N p (k+1)).eval i
    have hf (i) : 0 < F i := mul_pos (positive_kernel _ _ _ _ (H.levels.blocks ..).branches) (ih i)
    rw [(h.steps N p k hk).1]
    have hi : Integrable F (prior G _) := StepData.push_slice (H.levels.transition_mass ..) U _
      (((H.rep N p (k+1)).envelope (h.represents N p (k+1) hk).good).integrable _)
    apply (integral_pos_iff_support_of_nonneg (fun x => (hf x).le) hi).2
    rw [show Function.support F=Set.univ from Set.eq_univ_of_forall fun i => (hf i).ne']; simp

lemma chosen_shift (h : H.Selected) (hv : m≤N) (o : Site (H.S.side m p)) :
    (H.rep N p m).eval ∘ translate o = (H.rep N p m).eval := by
  induction hv using Nat.decreasingInduction with
  | self =>
    rw [(h.starts ..).2]; funext U
    simp only [Function.comp_apply]; rw [← pull_one]
    simp only [bare,energy_pull]
  | of_succ k hk ih =>
    rw [(h.steps N p k hk).1]
    rw [← commute_tr, ih]
    exact ((H.rep N p (k+1)).envelope (h.represents N p (k+1) hk).good).integrable _
end YM.Multi.AxisShift
