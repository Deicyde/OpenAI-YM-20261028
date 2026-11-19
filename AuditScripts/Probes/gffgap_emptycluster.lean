import ChallengeSpec

/-! Audit probe (GFF completeness follow-up). Not part of the submission.
For an empty cluster `I = Empty`, `Within` is vacuous, `weight = 0`, and the coefficients do not
depend on `r`. The OPE then forces (a) every empty-cluster coefficient of grade `j ≥ 1` to vanish
and (b) the grade-0 truncation to be an exact identity for every spectator word. Any witness
(a generalized free field included) therefore needs grade-0 actors whose insertion at `o`
reproduces every spectator correlation, i.e. an identity field in `Field 0`. -/

set_option autoImplicit false
noncomputable section
open YangMills Filter Topology

namespace GFFGapProbe
variable {g : GaugeGroup} {C : WilsonFamily g} (T : Hierarchy C)

theorem weight_empty (a : Empty → T.Tag) : T.weight a = 0 := by
  simp [Hierarchy.weight]

/-- The weight reads the grade index of each tag, not any intrinsic dimension. -/
theorem weight_single (a : Unit → T.Tag) : T.weight a = ((a ()).1 : ℝ) := by
  simp [Hierarchy.weight]

theorem within_empty (r M η : ℝ) (x : Empty → Spacetime) (o : Spacetime) :
    Hierarchy.Within r M η x o :=
  ⟨fun i => i.elim, fun i => i.elim⟩

theorem rpow_tendsto_zero (p : ℝ) (hp : 0 < p) :
    Tendsto (fun r : ℝ => r ^ p) (𝓝[>] 0) (𝓝 0) := by
  have h := Real.continuousAt_rpow_const 0 p (Or.inr hp.le)
  have h0 : (0:ℝ) ^ p = 0 := Real.zero_rpow hp.ne'
  rw [ContinuousAt, h0] at h
  exact tendsto_nhdsWithin_of_tendsto_nhds h

theorem empty_coeff_zero (hO : T.OperatorProductExpansion) (a : Empty → T.Tag)
    (j : ℕ) (hj : 1 ≤ j) (i : T.Channel j) (x : Empty → Spacetime) (o : Spacetime) :
    T.coefficient a j i x o = 0 := by
  have h := hO.coefficients a 0 1 (1/2) le_rfl one_pos (by norm_num) j i
  have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖T.coefficient a j i x o‖ ≤ r ^ ((j:ℝ) - 0 - 1/2) := by
    filter_upwards [h] with r hr
    have := hr x o (within_empty r 0 1 x o)
    rwa [weight_empty] at this
  have hp : (0:ℝ) < (j:ℝ) - 0 - 1/2 := by
    have : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
    linarith
  have h0 := ge_of_tendsto (rpow_tendsto_zero _ hp) hb
  exact norm_le_zero_iff.mp h0

theorem empty_cluster_exact (hO : T.OperatorProductExpansion) {J : Type} [Fintype J]
    (a : Empty → T.Tag) (b : J → T.Tag) (c : ℝ) (hc : 0 < c) (D : ℕ)
    (x : Empty → Spacetime) (o : Spacetime) (y : J → Spacetime)
    (hy : Hierarchy.Clear o y c) (s : Option T.Character) :
    T.grouped s a x b y =
      ∑ j : Fin (D+1), ∑ i : T.Channel j.val, T.coefficient a j.val i x o *
        T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y := by
  have h := hO.remainder a b 0 1 c (1/2) le_rfl one_pos hc (by norm_num) D
  have hb : ∀ᶠ r : ℝ in 𝓝[>] 0, ‖T.grouped s a x b y - ∑ j : Fin (D+1), ∑ i : T.Channel j.val,
      T.coefficient a j.val i x o *
        T.grouped s (fun _ : Unit => ⟨j.val, T.actor j.val i⟩) (fun _ => o) b y‖
        ≤ r ^ ((D:ℝ) + 1 - 0 - 1/2) := by
    filter_upwards [h] with r hr
    have := hr x o y (within_empty r 0 1 x o) hy s
    rwa [weight_empty] at this
  have hp : (0:ℝ) < (D:ℝ) + 1 - 0 - 1/2 := by
    have : (0:ℝ) ≤ (D:ℝ) := Nat.cast_nonneg D
    linarith
  have h0 := ge_of_tendsto (rpow_tendsto_zero _ hp) hb
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

/-- Grade-0 actors alone reproduce every spectator correlation (an identity field is needed). -/
theorem identity_channel_needed (hO : T.OperatorProductExpansion) {J : Type} [Fintype J]
    (a : Empty → T.Tag) (b : J → T.Tag) (c : ℝ) (hc : 0 < c)
    (x : Empty → Spacetime) (o : Spacetime) (y : J → Spacetime)
    (hy : Hierarchy.Clear o y c) (s : Option T.Character) :
    T.grouped s a x b y = ∑ i : T.Channel 0, T.coefficient a 0 i x o *
        T.grouped s (fun _ : Unit => ⟨0, T.actor 0 i⟩) (fun _ => o) b y := by
  rw [empty_cluster_exact T hO a b c hc 0 x o y hy s]
  first
  | exact Fin.sum_univ_one _
  | (simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]; done)
  | (simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]; rfl)

end GFFGapProbe

#print axioms GFFGapProbe.weight_single
#print axioms GFFGapProbe.empty_coeff_zero
#print axioms GFFGapProbe.empty_cluster_exact
#print axioms GFFGapProbe.identity_channel_needed
