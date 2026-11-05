import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Flat
import YM.Work.B18


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Flat accounting on the *same* horizon

Gram is in actual tree/frozen coordinates. Identify separately the
uncut Hessian check (on all-tree-free keys), not presuming it works
identically after the cuts used by the RG integral.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Flat
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
  YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
  YM.Next.Fluctuations YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented Rows YM.Work.F03
open scoped Topology BigOperators Classical InnerProductSpace ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} (T : Tube G S) {E σ Λ : ℝ}
variable (k : S.Choices)

/-- Tail on the flat check in each channel. -/
def omitted (r : ℝ) (a : Directions G f) : LogArray G (Slots S) := fun i =>
  i.2.elim (fun j => if j.2 then ∑' l : ℕ, let slot := (T.up.row j.1.2 l).2
    if till r < slot.length then (T.up.row j.1.2 l).1 • faceCurl (slotFace slot j.1.1)
      (pulled (labels a) i.1) else 0 else 0) (fun _ => 0)

lemma ideal_checks (hT : T.up.Bounds T.high σ E Λ) (h : S.patch.Branches S.kernel G) (r : ℝ) (a : Directions G f) :
    ideal T a=bump T r 1 k a + omitted T r a := by
  funext i
  obtain ⟨s,p|b⟩ := i
  · simp only [ideal, Pi.add_apply,bump,omitted,xLin,faceKick,Sum.elim_inl]
    split
    · have hz : pulled (labels (0:Directions G f)) s = 0 := by funext i; unfold pulled labels; dsimp only [Pi.zero_apply]; split <;> simp
      simp_rw [flat_curl, barrel, facade_all,hz,YM.Push.stroll_zero,G.adjoint_one]
      let u (l : ℕ) := (T.up.row p.1.2 l).1 • faceCurl (slotFace (T.up.row p.1.2 l).2 p.1.1) (pulled (labels a) s)
      let v (l : ℕ) := (T.up.row p.1.2 l).2.length ≤ till r
      have hd : Summable u := ellLine_summable T.up hT _ _
      have hr (v : ℕ → Prop) : Summable (fun l => if v l then u l else 0) := by
        refine Summable.of_norm_bounded hd.norm ?_
        intro i; split
        · rfl
        · rw [norm_zero]; exact norm_nonneg _
      change ∑' i, u i = (∑' l, if v l then u l else 0)+ ∑' l, if till r < _ then u l else 0
      rw [show (fun l => if till r < (T.up.row p.1.2 l).2.length then u l else 0)=(fun l => if ¬v l then u l else 0) from by
        funext i; simp [v]]
      have hm := (hr v).tsum_add (hr (fun l => ¬v l))
      refine (tsum_congr (fun i => (show u i = (if v i then u i else 0)+(if ¬v i then u i else 0) by split_ifs <;> simp))).trans ?_
      convert! hm using 1 <;> congr! 3 <;> (split <;> simp [*])
    next t => simp [flat_curl]
  · simp only [ideal, Pi.add_apply,bump,omitted,Sum.elim_inr,zLin,noiseKick,flat_probe _ _ _ _ h,bills,Pi.zero_apply,zero_sub,smul_neg,add_zero]; rfl

section metric
variable (H : Precision.Bed) (F : Forest S.ratio) {o v : ℝ}









end metric
end YM.Next.SectorChange.Flat
