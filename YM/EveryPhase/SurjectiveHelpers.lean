import YM.Next.BOUNDARY.Heights
import YM.Work.B14

/-!
# Auxiliary results for phase reconstruction
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory
open Boundary OS
open scoped Topology InnerProductSpace BigOperators NNReal ContDiff
variable {n : ℕ}

lemma margins_exists {y : Heights n} (h : y∈positiveHeight n) : ∃ p : ℝ≥0, (p,y)∈margins n := by
  let D := 𝓝[>] (0:ℝ≥0)
  have he {t : ℝ} (ht : 0<t) : ∀ᶠ p : ℝ≥0 in D, 4*(p:ℝ)<t := by
    have hz : Tendsto (fun p : ℝ≥0 => 4*(p:ℝ)) D (𝓝 0) := by
      simpa using! ((continuous_const.mul (f:=fun p : ℝ≥0 => (4:ℝ)) continuous_subtype_val).tendsto
        (0:ℝ≥0) |>.mono_left (nhdsWithin_le_nhds (s:=Ioi 0)))
    exact hz.eventually (gt_mem_nhds ht)
  have hh : ∀ᶠ p : ℝ≥0 in D, ∀ i j : Fin n, i<j → 4*(p:ℝ)<y j-y i :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun u => he (sub_pos.mpr (h.1 u))
  have hx : ∀ᶠ p : ℝ≥0 in D, p<1 := (eventually_lt_nhds (by norm_num : (0:ℝ≥0)<1)).filter_mono
    nhdsWithin_le_nhds
  have hp : ∀ᶠ p : ℝ≥0 in 𝓝[>] (0:ℝ≥0), (p,y) ∈ margins n := by
    change ∀ᶠ p : ℝ≥0 in D, (p,y) ∈ margins n
    filter_upwards [hx, hh, self_mem_nhdsWithin, eventually_all.mpr (fun i => he (h.2 i))] with i hi hu hq hk
    exact ⟨h, ⟨hq, hi, hu⟩, hk⟩
  exact hp.exists

end YM.Next.BOUNDARY
