import ChallengeSpec

/-! Regression check for the compact-set formulation of the input challenge.
The public estimates imply uniform bounds on scaled compact cluster shapes and on
compact spectator configurations separated from each other and from the origin. -/
set_option autoImplicit false
noncomputable section
namespace YangMills.CompactCheck
open Set Function MeasureTheory Filter Hierarchy
open scoped Topology BigOperators Classical

private theorem smallLower {X : Type} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (f : X → ℝ) (hf : Continuous f) (hp : ∀ x ∈ K, 0 < f x) :
    ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ x ∈ K, c ≤ f x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne hf.continuousOn
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (hp x hx))] with c hc
  exact fun y hy => hc.le.trans (hmin hy)

private theorem bounds {n : ℕ} {K : Set (Points n)} (hK : IsCompact K)
    (sep : ∀ x ∈ K, Injective x.ofLp) :
    ∃ M η : ℝ, 0 ≤ M ∧ 0 < η ∧ ∀ x ∈ K, ∀ r : ℝ, 0 < r →
      Within r M η (fun i => r • x i) 0 := by
  have upper (i : Fin n) : ∀ᶠ M : ℝ in atTop, ∀ x ∈ K, ‖x i‖ ≤ M := by
    rcases K.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨x,hx,hmax⟩ := hK.exists_isMaxOn hne
      ((PiLp.continuous_apply 2 _ i).norm.continuousOn)
    filter_upwards [eventually_ge_atTop ‖x i‖] with M hM y hy using (hmax hy).trans hM
  have lower (i j : Fin n) : ∀ᶠ c : ℝ in 𝓝[>] 0, i ≠ j → ∀ x ∈ K, c ≤ ‖x i-x j‖ := by
    by_cases e : i=j
    · simp [e]
    · apply (smallLower hK _ ((PiLp.continuous_apply 2 _ i).sub (PiLp.continuous_apply 2 _ j)).norm
        (fun x hx => norm_pos_iff.mpr (sub_ne_zero.mpr ((sep x hx).ne e)))).mono
      exact fun _ hc _ => hc
  obtain ⟨M,hM,hu⟩ := ((eventually_ge_atTop (0:ℝ)).and (eventually_all.mpr upper)).exists
  have pos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  obtain ⟨η,hη,hl⟩ := (pos.and (eventually_all.mpr fun i => eventually_all.mpr (lower i))).exists
  refine ⟨M,η,hM,hη,fun x hx r hr => ⟨fun i => ?_,fun i j hij => ?_⟩⟩
  · rw [sub_zero,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
    exact mul_le_mul_of_nonneg_right (hu i x hx) hr.le
  · rw [← smul_sub,norm_smul,Real.norm_of_nonneg hr.le,mul_comm]
    exact mul_le_mul_of_nonneg_left (hl i j hij x hx) hr.le

private theorem outside {n : ℕ} {Y : Set (Points n)} (hY : IsCompact Y)
    (sep : ∀ y ∈ Y, Injective (Fin.cons (0:Spacetime) y.ofLp)) :
    ∃ c : ℝ, 0 < c ∧ ∀ y ∈ Y, Clear 0 y.ofLp c := by
  have ext (i : Fin n) : ∀ᶠ c : ℝ in 𝓝[>] 0, ∀ y ∈ Y, c ≤ ‖0-y i‖ := by
    apply smallLower hY _ (continuous_const.sub (PiLp.continuous_apply 2 _ i)).norm
    intro y hy
    exact norm_pos_iff.mpr (sub_ne_zero.mpr ((sep y hy).ne (Fin.succ_ne_zero i).symm))
  have pair (i j : Fin n) : ∀ᶠ c : ℝ in 𝓝[>] 0, i ≠ j → ∀ y ∈ Y, c ≤ ‖y i-y j‖ := by
    by_cases e : i=j
    · simp [e]
    · apply (smallLower hY _ ((PiLp.continuous_apply 2 _ i).sub (PiLp.continuous_apply 2 _ j)).norm
        (fun y hy => norm_pos_iff.mpr (sub_ne_zero.mpr ((sep y hy).ne (Fin.succ_injective _ |>.ne e))))).mono
      exact fun _ hc _ => hc
  have pos : ∀ᶠ c : ℝ in 𝓝[>] 0, 0 < c := self_mem_nhdsWithin
  obtain ⟨c,hc,he,hp⟩ := (pos.and ((eventually_all.mpr ext).and (eventually_all.mpr fun i => eventually_all.mpr (pair i)))).exists
  exact ⟨c,hc,fun y hy => ⟨fun i => he i y hy,fun i j hij => hp i j hij y hy⟩⟩

variable {g : GaugeGroup} {C : WilsonFamily g} {T : Hierarchy C}
theorem compactCoefficient (ope : T.OperatorProductExpansion) {n : ℕ} (a : Fin n → T.Tag)
    (j : ℕ) {K : Set (Points n)} (hK : IsCompact K) (sep : ∀ x ∈ K, Injective x.ofLp)
    {ε : ℝ} (hε : 0 < ε) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ x ∈ K,
    ‖∑ i : T.Channel j, T.coefficient a j i (fun k => r • x k) 0 • T.actor j i‖ ≤
      B * r ^ ((j:ℝ) - T.weight a - ε) := by
  obtain ⟨M,η,hM,hη,h⟩ := bounds hK sep
  refine ⟨∑ i : T.Channel j, ‖T.actor j i‖,Finset.sum_nonneg (fun _ _ => norm_nonneg _),?_⟩
  have pos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [pos,eventually_all.mpr (ope.coefficients a M η ε hM hη hε j)] with r hr he x hx
  apply (norm_sum_le ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul,mul_comm]
  exact mul_le_mul_of_nonneg_left (he i _ 0 (h x hx r hr)) (norm_nonneg _)

theorem compactRemainder (ope : T.OperatorProductExpansion) {n m : ℕ} (a : Fin n → T.Tag)
    (b : Fin m → T.Tag) (D : ℕ) {K : Set (Points n)} {Y : Set (Points m)}
    (hK : IsCompact K) (sep : ∀ x ∈ K, Injective x.ofLp) (hY : IsCompact Y)
    (exterior : ∀ y ∈ Y, Injective (Fin.cons (0:Spacetime) y.ofLp)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, ∀ s x, x ∈ K → ∀ y ∈ Y,
    ‖T.grouped s a (fun k => r • x k) b y.ofLp -
      ∑ j : Fin (D+1), ∑ i : T.Channel j.val, T.coefficient a j.val i (fun k => r • x k) 0 *
        T.grouped s (fun _ : Unit => ⟨j.val,T.actor j.val i⟩) (fun _ => 0) b y.ofLp‖
      ≤ r ^ ((D:ℝ)+1-T.weight a-ε) := by
  obtain ⟨M,η,hM,hη,h⟩ := bounds hK sep
  obtain ⟨c,hc,hy⟩ := outside hY exterior
  have pos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  filter_upwards [pos,ope.remainder a b M η c ε hM hη hc hε D] with r hr he s x hx y hy'
  exact he _ 0 _ (h x hx r hr) (hy y hy') s
end YangMills.CompactCheck

open Lean Elab Command in
run_cmd do
  for n in [`YangMills.CompactCheck.compactCoefficient, `YangMills.CompactCheck.compactRemainder] do
    let axioms ← collectAxioms n
    unless axioms.all ([`propext, `Quot.sound, `Classical.choice] : List Name).contains do
      throwError "Unexpected compact estimate axiom at {n}"
    logInfo m!"COMPACT_ESTIMATE {n} {axioms}"
