import Construction

/-- The core comparator asks only for existence, reconstruction, the OPE and the trace test. -/
theorem YangMills.jointExistence : YangMills.JointExistence := by
  intro g hg
  obtain ⟨C,_,_,reg,orders⟩ := YangMills.constructed.{0,0} g hg 1 zero_lt_one
  refine ⟨YangMills.wilsonFamily C,reg,fun p hp => ?_⟩
  let a : YM.Extraction.Order := ⟨.full,⟨p,hp⟩⟩
  obtain ⟨q,S,F,L,Q,M,X,core,_⟩ := orders a
  exact ⟨q.per,q.per.monotone,YangMills.hierarchy F Q,core⟩
