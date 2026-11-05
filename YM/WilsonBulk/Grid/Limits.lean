import YM.WilsonBulk.Grid.Dual
import YM.WilsonBulk.Grid.Age
import YM.UVExtension.Free.Rows

/-! Completeness for our frozen-width UV demands with bounds. Do NOT lose
precision in a subsequence relation. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open Lattice Laurent Filter Function Bloch
open Push.AbsoluteSums RG Finset Work.F08 UVExtension.Free
open scoped Topology BigOperators Classical
variable {α β γ : Type*}

lemma tight_entry {η B : ℝ} {R : Row α β} (h : R.strip η B) (hη : 0 ≤ η) (a b x) : ‖R a b x‖ ≤ B :=
  budget_single ((h a b).unweighted hη) _

-- general monotone comparison caps with possible fine-scale dependence
lemma release {m₀ : ℕ} {R : ℕ → Row α β} {A η : ℝ} {F : ℕ → ℝ}
    (hη : 0 ≤ η) (H : ∀ᶠ n in atTop, (R n).strip η A)
    (hF : Tendsto F atTop (𝓝 0)) (d : ∀ m n, m₀ ≤ m → m ≤ n →
      (minusRows (R m) (R n)).strip η (F m)) :
    ∃ T, T.strip η A ∧ Tendsto R atTop (𝓝 T) ∧
      ∀ m, m₀ ≤ m → (minusRows (R m) T).strip η (F m) := by
  have hu x y z : CauchySeq (fun n => R n x y z) := by
    refine Metric.cauchySeq_iff'.2 fun ε hε=> ?_
    obtain ⟨l,hl,hk⟩ := ((hF.eventually (gt_mem_nhds hε)).and (eventually_ge_atTop m₀)).exists
    refine ⟨l,fun u h => ?_⟩
    rw [dist_comm,dist_eq_norm]; exact lt_of_le_of_lt (tight_entry (d l u hk h) hη x y z) hl
  choose t ht using fun x y z => cauchySeq_tendsto_of_complete (hu x y z)
  have h : Tendsto R atTop (𝓝 t) :=
    tendsto_pi_nhds.mpr fun x => tendsto_pi_nhds.mpr fun y => tendsto_pi_nhds.mpr fun z=> ht x y z
  refine ⟨t, UVExtension.Free.inherits h H, h, fun m hm=> UVExtension.Free.inherits (R:=fun n => minusRows (R m) (R n)) ?_ ?_⟩
  · exact tendsto_const_nhds (x:=R m) |>.sub h
  exact (eventually_ge_atTop m).mono fun i hi=> d m i hm hi

lemma release_received [Fintype α] [Fintype β] {m₀ : ℕ} {R : ℕ → Row α β}
    {A η : ℝ} {F : ℕ → ℝ} (hη : 0≤ η) (H : ∀ᶠ n in atTop, (R n).strip η A)
    (hF : Tendsto F atTop (𝓝 0)) (d : ∀ m n, m₀ ≤ m → m ≤ n →
      (minusRows (R m) (R n)).strip η (F m)) :
    ∃ T, Received R T η A ∧ ∀ m, m₀ ≤ m → (minusRows (R m) T).strip η (F m) := by
  obtain ⟨T,hX,h,hv⟩:= release hη H hF d
  exact ⟨T,reported h H,hv⟩

end YM.WilsonBulk
