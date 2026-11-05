import YM.EveryPhase.Compatibility

/-!
# Partial-boundary limits for derivative tests
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY

open Set Filter Function MeasureTheory
open Boundary OS Spec Org
open scoped Topology InnerProductSpace NNReal ENNReal

/-- Nontrivial approach even at any of the spectator partial boundaries. -/
lemma towards_shore {n : ℕ} {x : Points n} (hx : x∈shores n) : (𝓝[fields n] x).NeBot := by
  let y := dawn (rate n)
  have he : Tendsto (fun t : ℝ => x+t • y) till (𝓝[fields n] x) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa using (tendsto_const_nhds (x:=x)).add
        ((tendsto_id (x:=(𝓝 (0:ℝ)))).smul (tendsto_const_nhds (x:=y)) |>.mono_left
          (nhdsWithin_le_nhds (s:=Ioi 0)))
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' := mem_Ioi.mp ht
    have hy : y∈fields n := etched (fun i j hij => by unfold rate; exact_mod_cast hij)
    simp only [shores, fields, mem_iInter, mem_setOf_eq] at hx hy ⊢
    intro i j hij
    change (x j+t • y j)-(x i+t • y i)∈Mink.inside
    rw [show (x j+t • y j)-(x i+t • y i)=x j-x i+t • (y j-y i) by rw [smul_sub]; abel]
    change ‖spatial _‖ < time _
    rw [Mink.rest_add, Mink.clock_add, Mink.rest_mul, Mink.clock_mul]
    refine lt_of_le_of_lt (norm_add_le _ _) ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht']
    exact add_lt_add_of_le_of_lt (hx i j hij) (mul_lt_mul_of_pos_left (hy i j hij) ht')
  exact he.neBot

end YM.Next.BOUNDARY
