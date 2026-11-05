import YM.MultipleContact.Tests
set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact
open Function Filter MeasureTheory Set TopologicalSpace Metric
open scoped Topology BigOperators ContDiff Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
lemma exists_jetBounds_of_bounded {f:E→ℂ}(hf:ContDiff ℝ ∞ f){M:ℝ}(hm : ∀ x, f x ≠ 0 → ‖x‖ ≤ M) (n:ℕ) :
      ∃ C,JetBounds n f C:=by
     let U:Opens E:=⊤
     have ht : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall ..) fun x (hx:x∉closedBall 0 M)=> (by exact not_ne_iff.mp (fun hW=>hx ((Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using hm x hW))))) -- edit
     let g: TestFunction U ℂ ⊤ := ⟨f,hf,ht,subset_univ _⟩
     exact has_bound g n
lemma exists_scaled_jetBounds {f:E→ℂ}(hf:ContDiff ℝ ∞ f){M:ℝ}(hm : ∀ x, f x ≠ 0 → ‖x‖ ≤ M)(n:ℕ){r:ℝ}(hr:0<r):
      ∃ C,JetBounds n (scaled r f) C:=by
    have hC:ContDiff ℝ ∞ (scaled r f):= (hf.comp (contDiff_const.smul contDiff_id)).const_smul _
    refine exists_jetBounds_of_bounded hC (fun x hx=> (le_of_eq (?_ : ‖x‖ = r*‖r⁻¹•x‖)).trans (mul_le_mul_of_nonneg_left (hm (r⁻¹ • x) (by intro he; apply hx; rw [scaled,he,smul_zero])) hr.le)) n
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos_of_pos hr)]; field_simp
end YM.MultipleContact
