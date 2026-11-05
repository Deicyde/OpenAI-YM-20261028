import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Year

/-!
# Marked *actual* determinant panels

One site mark may even change projection (flag/seed, trunk holes, ...).
All costs after mark scale with number of marked sites and polynomial(lB),
not with volume. As in E Pours at records, estimate doesn't require an
Allocation state proving positive probability of each formal Σ used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Function Filter Set Matrix MeasureTheory Lattice RG Wilson Pressure Tree
open Next.SectorChange FreeResolvent
 
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {A A' : Stores S} {k k' : S.Choices}
    {F H : Forest S.ratio} {V V' : Config G c} {x v C η b d a : ℝ} {l B : ℕ}













lemma Certified.writes (h : Certified S T x v C η b) (F : Forest S.ratio) (k : S.Choices)
    (hp : A.flags=RG.flags (temp x) V) :
    Priced (native c) (place S) (windows S x) (AFull T A F x V k) v C (currency b (radiusB x)) :=
  (h.text A F k V hp).2.2.2
lemma Certified.fogs (h : Certified S T x v C η b) (F : Forest S.ratio) (k : S.Choices)
    (hp : A.flags=RG.flags (temp x) V) : Schur.clouded (windows S x) (AFull T A F x V k)=CFull T A F x V k ∧
      (Schur.clouded (windows S x) (AFull T A F x V k)).PosDef := by
  have he := h.text _ F k _ hp
  have ht := produced T A F h.basis V k h.precision he.1
  exact ⟨ht,ht.symm ▸ c_pos T A F _ he.2.2.1⟩
lemma Certified.excessive (h : Certified S T x v C η b) (F : Forest S.ratio) (k : S.Choices)
    (hp : A.flags=RG.flags (temp x) V) :
    (1+excess (windows S x) (AFull T A F x V k)).det =
      (1 + (Rows.gram T x V k (shots S x) A F * fog A F T x V k - 1)).det := by
  let P := AFull T A F x V k
  unfold excess
  have hz {ι : Type} (u : Square ι) [DecidableEq ι] : 1 + (u-1) = u := by abel
  rw [(h.fogs F k hp).1,hz,hz,Matrix.det_mul,Matrix.det_mul,c_det,a_det]



end YM.AnalyticBridge.RelativeLogdet.Physical
