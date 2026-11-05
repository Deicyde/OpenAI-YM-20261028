import Mathlib.Analysis.Normed.Group.Tannery
import YM.Ovens.Coffee

/-!
# Continuity at fixed dictionary: why a subsequence domination test works

From any parameters converging to x in the domain of a Curve choose a
subsequence paying even the full absolute `P.mass` on pre-mask jet
deviations. No continuity in a Regime parameter or near
blowing-up geometry, no assertion that one summable majorant over **whole**
parameter intervals is necessary/always available.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Progress.DirectedRecipe

open Function Set RG Wilson Lattice RG.Shoot Ovens Ovens.Pipes Filter
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {P : BudgetPoint}

namespace Samples
section Pay
lemma one_le_quote {f : ℕ → ℝ} {c : ℝ} (h : SumBudget f c) (i : ℕ) : f i ≤ c := by
  simpa using (h.2.1.sum_le_tsum {i} (fun j _ => h.1 j)).trans h.2.2

-- apply to both per-parameter changes
lemma overhead (P : BudgetPoint) {F : ℕ → ℕ → ℝ} (hu : ∀ n i, 0 ≤ F n i)
    (X : ℕ → Support n) {c : ℕ → ℝ} {ε : ℝ} (h : HasSum c ε)
    (H : ∀ j, SumBudget (fun i => P.mass (X i) (F j i)) (c j)) :
    ∃ b : ℕ → ℝ, (∀ j i, F j i ≤ b i) ∧ SumBudget (fun i => P.mass (X i) (b i)) ε := by
  let f : ℕ → ℕ → ℝ := fun j i => P.mass (X i) (F j i)
  have hp j i : 0 ≤ f j i := (H j).1 i
  have hz : Summable fun j => ∑' i, f j i := Summable.of_nonneg_of_le
    (fun j => tsum_nonneg (hp j)) (fun j => (H j).2.2) h.summable
  have hs : Summable (Function.uncurry f) := (summable_prod_of_nonneg (fun x => hp x.1 x.2)).mpr
    ⟨fun j => (H j).2.1, hz⟩
  let b := fun i => ∑' j, F j i
  have hF i : Summable fun j => F j i := Summable.of_nonneg_of_le (fun j => hu j i)
    (fun j => P.loMass (X i) _ (hu j i)) (hs.prod_symm.prod_factor i)
  have hb (i) : P.mass (X i) (b i) = ∑' j, f j i := by
    unfold f b BudgetPoint.mass
    rw [tsum_mul_left]
  refine ⟨b,fun j i => ?_,⟨fun i => (hb i).ge.trans' (tsum_nonneg fun j => hp j i), ?_,?_⟩⟩
  · simpa only [Finset.sum_singleton] using (hF i).sum_le_tsum {j} (fun j _ => hu j i)
  · simp_rw [hb]; exact hs.prod_symm.prod
  rw [funext hb, hs.tsum_comm]
  exact (hz.tsum_le_tsum (fun j => (H j).2.2) h.summable).trans_eq h.tsum_eq

lemma warp (P : BudgetPoint) (X : ℕ → Support n) (L : ℕ → Prop) [DecidablePred L] {c d : ℕ → ℝ} {a b : ℝ}
    (h : SumBudget (fun i => if L i then P.mass (X i) (c i) else 0) a)
    (hp : SumBudget (fun i => P.mass (X i) (d i)) b) :
    SumBudget (fun i => if L i then P.mass (X i) (c i + d i) else 0) (a+b) := by
  let A i := if L i then P.mass (X i) (c i) else 0
  let B i := P.mass (X i) (d i)
  let D i := if L i then B i else 0
  have hd i : 0 ≤ D i := by
    unfold D; split
    · exact hp.1 i
    exact le_rfl
  have he i : D i ≤ B i := by
    unfold D; split
    · exact le_rfl
    exact hp.1 i
  have hD := Summable.of_nonneg_of_le hd he hp.2.1
  have hJ : ∑' i, D i ≤ b := (hD.tsum_le_tsum he hp.2.1).trans hp.2.2
  have hm (i) : A i + D i = if L i then P.mass (X i) (c i + d i) else 0 := by
    by_cases hi : L i <;> simp [*,A,B,D,BudgetPoint.mass,mul_add]
  rw [← funext hm]; refine ⟨fun i => add_nonneg (h.1 i) (hd i), h.2.1.add hD, ?_⟩
  rw [Summable.tsum_add h.2.1 hD]
  exact add_le_add h.2.2 hJ
end Pay

lemma within {a : Set ℝ} {x} {s : ℕ → ℝ} (hi : ∀ i, s i∈a) (he : Tendsto s atTop (𝓝 x)) :
    Tendsto s atTop (𝓝[a] x) := tendsto_nhdsWithin_iff.mpr ⟨he,Eventually.of_forall hi⟩

/-- A sampling set INCLUDES the base point. -/
def sample (x : ℝ) (s : ℕ → ℝ) := insert x (range s)

lemma sample_sub {a : Set ℝ} {x s} (hx : x∈a) (h : ∀ i, s i∈a) : sample x s ⊆ a :=
  insert_subset hx (range_subset_iff.mpr h)

lemma sample_map (x : ℝ) (s : ℕ → ℝ) (j : ℕ) : s j∈sample x s := mem_insert_of_mem _ (mem_range_self _)

variable {A : ℝ → Activities G n}

/-- Across all points including x and *all* s, not just eventually in subsequence index. -/
structure Shared (P : BudgetPoint) (A : ℝ → Activities G n) (x : ℝ) (T : Set ℝ) (δ w : ℝ) : Prop where
  B (a) : a∈T → (A a).reg = (A x).reg
  C (a) : a∈T → (A a).forced = (A x).forced
  E : ∃ b : ℕ → ℝ, (∀ y : Site n, SumBudget (fun i => if ((A x).reg i).site=y then
        P.mass ((A x).reg i).support (b i) else 0) δ) ∧
      ∀ a∈T, ∀ i, P.supBounds ((A x).reg i).site ((A x).reg i).support ((A a).E i) (b i)
  K : ∃ b : ℕ → ℝ, (∀ y : Site n, SumBudget (fun i => if y∈((A x).forced i).support then
        P.mass ((A x).forced i).support (b i) else 0) w) ∧
      ∀ a∈T, ∀ i, (0 ≤ b i) ∧ ∀ U, ‖(A a).K i U‖ ≤ b i

lemma along {T : Set ℝ} {x : ℝ} (hx : x∈T) (s : ℕ → ℝ) (h : ∀ i, s i∈T)
    (hl : Tendsto s atTop (𝓝 x)) {Q : ℝ → Rep G n} (p : Curve P Q T)
    {δ w : ℝ} (hp : (Q x).activities.Valid P δ w) {ε : ℝ} (he : 0 < ε) :
    ∃ r : ℕ → ℕ, StrictMono r ∧ Shared P (fun i => (Q i).activities) x (sample x (s ∘ r)) (δ+ε) (w+ε) := by
  let c (i : ℕ) := (ε/2)*(1/2:ℝ)^i
  have hc : HasSum c ε := by
    have hz : HasSum c ((ε/2)*2) := hasSum_geometric_two.mul_left _
    rwa [div_mul_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)] at hz
  have hi i : 0 < c i := by unfold c; positivity
  choose m hm using fun i => eventually_atTop.1 ((within h hl).eventually (p.continuous (c i) (hi i) x hx))
  -- a subsequence above all the cuts; permits also absolutely summing at the SAME label
  let r (i : ℕ) := i + (Finset.range (i+1)).sup m
  have hu i : m i≤r i := le_trans (Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self _))) (Nat.le_add_left _ _)
  have H : StrictMono r := fun i j hij => add_lt_add_of_lt_of_le hij (Finset.sup_mono (Finset.range_mono
    (Nat.add_le_add_right hij.le _)))
  have hy := sample_sub hx (fun i => show (s ∘ r) i ∈ T from h (r i))
  choose C D hr hw hC hD using fun i => hm i (r i) (hu i)
  let A := (Q x).activities
  obtain ⟨a,ha,hA⟩ := hp.boundE
  obtain ⟨b,hb,hB⟩ := hp.boundK
  obtain ⟨f,hf,hs⟩ := overhead P (fun j i => (hr j i).1) (fun i => (A.reg i).support) hc hC
  obtain ⟨g,hg,hg'⟩ := overhead P (fun j i => (hw j i).1) (fun i => (A.forced i).support) hc hD
  have hbump {F F' a a' : ℝ} (hv : ‖F‖ ≤ a) (hs : ‖F-F'‖ ≤ a') : ‖F'‖ ≤ a+a' := by
    rw [norm_sub_rev] at hs
    have ht := (norm_add_le (F'-F) F).trans (add_le_add hs hv)
    rwa [sub_add_cancel, add_comm a'] at ht
  refine ⟨r,H,⟨fun y hh => p.reg y (hy hh) x hx, fun y hh => p.forced y (hy hh) x hx,
    ⟨fun i => a i + f i,fun y => warp P _ _ (hA y) hs,?_⟩,
    ⟨fun i => b i+g i,fun y => warp P _ _ (hB y) hg',?_⟩⟩⟩
  · intro y hh i
    have hJ : 0 ≤ f i := le_trans (hr 0 i).1 (hf 0 i)
    refine ⟨add_nonneg (ha i).1 hJ,?_⟩
    rcases hh with (rfl | ⟨j,rfl⟩)
    · exact fun U hU l hL hu => ((ha i).2 U hU l hL hu).trans (le_add_of_nonneg_right hJ)
    exact fun U hU l hL hu => hbump ((ha i).2 U hU l hL hu) (((hr j i).2 U hU l hL hu).trans (hf j i))
  intro y hh i
  have HJ : 0 ≤ g i := le_trans (hw 0 i).1 (hg 0 i)
  refine ⟨add_nonneg (hb i).1 HJ,?_⟩
  rcases hh with (rfl|⟨j,rfl⟩)
  · exact fun U => ((hb i).2 U).trans (le_add_of_nonneg_right HJ)
  exact fun U => hbump ((hb i).2 U) (((hw j i).2 U).trans (hg j i))

end Samples
end YM.Progress.DirectedRecipe
