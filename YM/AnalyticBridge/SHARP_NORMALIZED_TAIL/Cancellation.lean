import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Requests

/-!
# Local cancellation with simultaneous requests

At finite volume the unforced disjoint-family log is legitimate by the
`Sufficient` hit budget; no nonvanishing assumption. The price of an owner
involves ONLY that owner's physical `supp` in that log. Thus we can keep the
exponential suppression per requested token, not paying any power of the
volume (where requests are not themselves extensive).
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.Sharp
open Finset Function Filter RG
open SectorNext.Vacuum.ReLog
open scoped Topology BigOperators Classical

variable {J ι E : Type*} [Fintype J] [DecidableEq J] [DecidableEq E]



/-- One estimate at fixed volume suffices for absolute convergence of the
alphabet. Not a uniform bound on the unweighted sum. -/
lemma unweight [Fintype E] {U v : ι → ℝ} {ρ : E → ℝ} (r : ι → Finset E)
    (h : Summable v) (hp : ∀ t, 0 < ρ t) (hu : ∀ i, |U i| * (∏ t∈r i,ρ t) ≤ v i) : Summable U := by
  let s (u : Finset E) := ∏ t∈u,ρ t
  have he : ∃ ζ : ℝ, 0<ζ ∧ ∀ u, ζ≤s u := by
    obtain ⟨a,-,ha⟩ := Finset.exists_min_image (univ : Finset (Finset E)) s univ_nonempty
    exact ⟨_,prod_pos (s:=a) (fun i _ => hp i),fun t => ha t (mem_univ t)⟩
  obtain ⟨c,hc,H⟩ := he
  have hz (i) : ‖U i‖ ≤ v i * c⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hc]
    exact (mul_le_mul_of_nonneg_left (H _) (abs_nonneg _)).trans (hu i)
  exact Summable.of_norm_bounded (h.mul_right _) hz

namespace Claims
variable {M : Claims J ι E} {hard : Finset E}
  {u v : ι → ℝ} {w : Grid J} {a δ : ℝ} {ρ : E → ℝ}



private lemma rebate (hρ : ∀ t, 0<ρ t) (hh : ∀ t, t∉ hard → 1≤ρ t)
    (s : Finset E) (i : ι) (ht : hard ∩ M.tokens i ⊆ s) :
    (∏ t∈s∩M.tokens i,ρ t) ≤ ∏ t∈M.tokens i,ρ t :=
  prod_le_prod_of_subset_of_one_le inter_subset_right (fun i _ => (hρ i).le) fun t hi he =>
    hh t fun h => he (mem_inter.mpr ⟨ht (mem_inter.mpr ⟨h,hi⟩),hi⟩)
















end Claims
end YM.AnalyticBridge.Sharp
