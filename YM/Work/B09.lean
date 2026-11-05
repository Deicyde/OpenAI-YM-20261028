import YM.Bid.Phase
import YM.Work.B09.Differential
import YM.Work.B09.Shell



/-! Transfer to *every* character with these whole-word values. -/
set_option autoImplicit false
noncomputable section
namespace YM.Work.B09

theorem answer : YM.Bid.B09 := by
  intro G C S V A P R H hl _ _ hA hP p hg i
  obtain ⟨φ, he⟩ := has_evaluator hP (hg.threads i)
  exact ⟨he.inclusions H hl.injection, he.derivatives hA, he.flux hA H hl.charges⟩

end YM.Work.B09
