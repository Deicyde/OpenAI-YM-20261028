import Mathlib


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Strong scalar response, including roots AT either end

No openness of income or trial data and no differentiability assertion for
the corrected branch. Boundary collisions (including a single legal trial)
need actual bracketing, not an estimate ignoring the truncated side. Even
the sign testers can depend on x, as long as all trials being compared are
legal for the response estimate at fixed x. Parameter continuity and inverse
stability in the presence of other perturbations, not just shooting once.
-/

set_option autoImplicit false
noncomputable section
namespace YM.UVNext.CouplingReset
open Set Filter Function
open scoped Topology

structure Response (s t : Set ℝ) (μ : ℝ) (F : ℝ → ℝ → ℝ) : Prop where
  margin : 0 < μ
  gain : ∀ x ∈ s, ∀ a ∈ t, ∀ b ∈ t, a ≤ b → μ*(b-a) ≤ F x b - F x a
  dial : ∀ x ∈ s, ContinuousOn (F x) t
  transport : ∀ a ∈ t, ContinuousOn (fun x => F x a) s

def TestsBracket (s t : Set ℝ) (lower upper : ℝ → ℝ) (F : ℝ → ℝ → ℝ) := ∀ x∈s,
    lower x ≤ upper x ∧ Icc (lower x) (upper x) ⊆ t ∧ F x (lower x) ≤ 0 ∧ 0 ≤ F x (upper x)

structure Zeroes (s t : Set ℝ) (F : ℝ → ℝ → ℝ) (d : ℝ → ℝ) : Prop where
  admissible : MapsTo d s t
  sol : ∀ x ∈ s, F x (d x) = 0

variable {s t : Set ℝ} {μ : ℝ} {F : ℝ → ℝ → ℝ} {d lo hi : ℝ → ℝ}

lemma Response.inverse (h : Response s t μ F) {x a b : ℝ} (hx : x ∈ s) (ha : a ∈ t) (hb : b ∈ t) :
    |b-a| ≤ |F x b - F x a| / μ := by
  wlog hh : a ≤ b generalizing a b
  · simpa [abs_sub_comm a b, abs_sub_comm (F x a)] using this hb ha (le_of_not_ge hh)
  rw [le_div_iff₀ h.margin,abs_of_nonneg (sub_nonneg.mpr hh),mul_comm]
  exact (h.gain x hx a ha b hb hh).trans (le_abs_self _)

lemma Response.posterior (h : Response s t μ F) (z : Zeroes s t F d) {x a : ℝ} (hx : x ∈ s) (ha : a ∈ t) :
    |d x-a| ≤ |F x a| / μ := by simpa [z.sol x hx] using h.inverse hx ha (z.admissible hx)



lemma Response.continuous (h : Response s t μ F) (z : Zeroes s t F d) : ContinuousOn d s := by
  intro x hx; apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) (eventually_of_mem self_mem_nhdsWithin
    fun y hy => h.posterior z hy (z.admissible hx)) ?_
  simpa [Real.norm_eq_abs,z.sol x hx] using (((h.transport _ (z.admissible hx) x hx).norm).tendsto.div_const μ)

lemma solve (h : Response s t μ F) (hb : TestsBracket s t lo hi F) : ∃ d, Zeroes s t F d ∧
    ContinuousOn d s ∧ ∀ x∈s, d x ∈ Icc (lo x) (hi x) := by
  have H (x : ℝ) : ∃ a, x ∈ s → a ∈ Icc (lo x) (hi x) ∧ F x a = 0 := by
    by_cases hx : x∈s
    · obtain ⟨hl,ht,h1,h2⟩ := hb x hx
      obtain ⟨a,ha,h⟩ := intermediate_value_Icc hl ((h.dial _ hx).mono ht) ⟨h1,h2⟩
      exact ⟨a,fun _ => ⟨ha,h⟩⟩
    exact ⟨0,fun h => False.elim (hx h)⟩
  choose d hd using H
  have hz : Zeroes s t F d := ⟨fun _ hx => (hb _ hx).2.1 (hd _ hx).1, fun x hx => (hd x hx).2⟩
  exact ⟨d,hz,h.continuous hz,fun x hx => (hd x hx).1⟩

lemma Response.balance {r : ℝ} (hr : 0 ≤ r) (h : Response s (Icc (-r) r) μ F) (h₀ : ∀ x∈s, |F x 0| ≤ μ*r) :
    TestsBracket s (Icc (-r) r) (fun _ => -r) (fun _ => r) F := by
  have hu : -r ≤ 0 := neg_nonpos.mpr hr
  intro x hx; have hF := abs_le.mp (h₀ x hx)
  have ha := h.gain x hx (-r) (left_mem_Icc.mpr (hu.trans hr)) 0 ⟨hu,hr⟩ hu
  have hb := h.gain x hx 0 ⟨hu,hr⟩ r (right_mem_Icc.mpr (hu.trans hr)) hr
  exact ⟨hu.trans hr,Subset.rfl,by linarith,by linarith⟩

lemma Response.balance_solve {r : ℝ} (hr : 0 ≤ r) (h : Response s (Icc (-r) r) μ F) (h₀ : ∀ x∈s, |F x 0| ≤ μ*r) :
    ∃ d, Zeroes s (Icc (-r) r) F d ∧ ContinuousOn d s := by
  obtain ⟨d,h1,h2,_⟩ := solve h (h.balance hr h₀)
  exact ⟨d,h1,h2⟩
end YM.UVNext.CouplingReset
