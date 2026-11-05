import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Boards
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Pockets

/-!
# Physical read of Gram entries

For the derivative of the Gram rows in SectorChange, there is an
important parsing shortcut with proof. A regular input direction can be
tested against **all rows**, since skip decisions outside its stencils
already have zero response (never delete a boundary row when taking a
principal window!). Use this even in a mark at a seed which deletes an
active slot. Off-domain the fderiv defaults in unused tentative rows
wouldn't be predicting smoothness -- only take values in the Formula.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Function Matrix Lattice RG Wilson Precision Pressure Tree
open Next.SectorChange Next.SectorChange.Completion
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {x : ℝ} (T : Tube G S)
  (k : S.Choices) (V : Config G c)

/-- Exact mask, no hypothesis of realizability (the existence here is
just `non-tree && not chilled`). -/
def openBond (A : Stores S) (F : Forest S.ratio) (x : ℝ) (i : Bond f) := ∃ j : Active A x F, j.val.val=i
lemma mask (A : Stores S) (F : Forest S.ratio) (x : ℝ) (i : Bond f) :
    openBond A F x i ↔ i∉F.trunks ∧ S.ratio.parent i.1∉A.dome (10*radiusB x) ∧
      S.ratio.parent (i.1+Lattice.step i.2)∉A.dome (10*radiusB x) := by
  constructor
  · rintro ⟨j,rfl⟩; refine ⟨j.val.property,fun h => j.property (Or.inl h),fun h => j.property (Or.inr h)⟩
  rintro ⟨h,hy,hz⟩; exact ⟨⟨⟨i,h⟩,not_or.mpr ⟨hy,hz⟩⟩,rfl⟩

/-- Same primitive rows as on tape, pulled as whole oriented functions. -/
def clue (x : ℝ) (i : Key G f) (r : Rows.Receipt G S) : ℝ :=
  (Rows.slip • Rows.bump T x V k (axisPrice i)) r.1 r.2

def unpaired (x : ℝ) (i j : Key G f) := ∑ r, clue T k V x i r * clue T k V x j r

lemma fresh_axis (A : Stores S) (F : Forest S.ratio) (z : Rows.In x A F (G:=G)) :
    Rows.fresh x (shots S x) A F (axisPrice z) = axisPrice (sorted A F (Sum.inl z)) := by
  rw [on_axis,on_axis]
  funext e
  by_cases h : e=z.1.val.val
  · subst e; rw [Gap.freshly_read,Pi.single_eq_same]
    change _ = Pi.single (M:=fun _=> G.Color) z.1.val.val (EuclideanSpace.basisFun G.ColorIndex ℝ z.2) z.1.val.val
    rw [Pi.single_eq_same]
  rw [Pi.single_eq_of_ne (show e≠(sorted A F (Sum.inl z)).1 from h)]
  unfold Rows.fresh
  split
  next hk =>
    split
    next hx => exact Pi.single_eq_of_ne (show (⟨⟨e,hk⟩,hx⟩:Active A x F) ≠ z.1 from fun hz => h (congr_arg (fun i : Active A x F => i.val.val) hz)) _
    next hx => rfl
  next hk => rfl

lemma to_clue (A : Stores S) (F : Forest S.ratio) (hS : S.patch.Branches S.kernel G) (r : Rows.Receipt G S) (i : Rows.In x A F (G:=G)) :
    Rows.move T x V k (shots S x) A F r i=clue T k V x (sorted A F (Sum.inl i)) r := by
  unfold Rows.move; rw [Matrix.of_apply,selected_all _ _ _ _ _ _ _ hS,fresh_axis]; rfl

lemma no_reserved (A : Stores S) (F : Forest S.ratio) (z : vacant A F x G) :
    ¬ openBond A F x z.val.1 := by
  rintro ⟨i,h⟩
  apply z.property; change ∃ (j : Rows.In x A F (G:=G)), _
  exact ⟨(i,z.val.2),Prod.ext h.symm rfl⟩

lemma warm_slot (A : Stores S) (F : Forest S.ratio) (i : Rows.In x A F (G:=G)) :
    openBond A F x (sorted A F (.inl i)).1 := ⟨i.1,rfl⟩

/-- Fully parsed through physical queries. No mask-specific
reidentification of the coordinates in `unpaired`. -/
theorem read_kernel (A : Stores S) (F : Forest S.ratio) (x : ℝ) (hS : S.patch.Branches S.kernel G) (i j) :
    AFull T A F x V k i j = if openBond A F x i.1 ∧ openBond A F x j.1 then unpaired T k V x i j else (1:Square (Key G f)) i j := by
  let e := sorted (G:=G) A F (x:=x)
  obtain ⟨i,rfl⟩ := e.surjective i
  obtain ⟨j,rfl⟩ := e.surjective j
  unfold AFull
  simp only [Matrix.submatrix_apply,e, Equiv.symm_apply_apply]
  rcases i with i|i <;> rcases j with j|j
  · rw [if_pos ⟨warm_slot A F i,warm_slot A F j⟩]
    change Rows.gram T x V k (shots S x) A F i j = _
    unfold Rows.gram unpaired
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro r _; rw [Matrix.transpose_apply]; rw [to_clue T k V A F hS r i,to_clue T k V A F hS r j]
  · rw [if_neg (fun hx => no_reserved A F j (hx.2))]
    change 0=(1:Square (Key G f)) (e (Sum.inl i)) (e (Sum.inr j))
    symm; rw [Matrix.one_apply_ne]
    simp
  · rw [if_neg (fun hx => no_reserved A F i hx.1)]
    change 0=(1:Square (Key G f)) (e (Sum.inr i)) (e (Sum.inl j))
    symm; rw [Matrix.one_apply_ne]
    simp
  rw [if_neg (fun hx => no_reserved A F i hx.1)]
  change (1:Square (vacant A F x G)) i j=(1:Square (Key G f)) (e (Sum.inr i)) (e (Sum.inr j))
  simp only [Matrix.one_apply,e.apply_eq_iff_eq]
  simp

lemma clue_zero (h : S.patch.Branches S.kernel G) (r : Rows.Receipt G S) (i : Key G f)
    (he : ¬ separation (Wisps.down S r) (place S i) ≤ Next.SectorChange.span S.patch x) : clue T k V x i r=0 := by
  rcases r with ⟨⟨s,u⟩,c⟩
  have hp := bump_dep T x V k s u (axisPrice i) 0 h (by
    intro e hx
    have hr : e ≠ i.1 := fun hy => by
      apply he
      rw [hy] at hx; exact (contains ..).1 hx
    rw [on_axis,Pi.single_eq_of_ne hr]; rfl)
  unfold clue; rw [Pi.smul_apply, hp]
  have hf : Rows.bump T x V k (0 : Directions G f) (s,u)=0 := by
    rcases u with j|j
    · simp only [Rows.bump,Sum.elim_inl]; unfold Rows.faceKick; simp [barrel]
    simp [Rows.bump,Rows.noiseKick]
  rw [hf,smul_zero]; rfl

lemma kernel_reach (h : S.patch.Branches S.kernel G) (x : ℝ) (A : Stores S) (F : Forest S.ratio) :
    Reaches (place S) (2*Next.SectorChange.span S.patch x) (AFull T A F x V k) := by
  intro i j hij
  rw [read_kernel _ _ _ _ _ _ h]; split
  · unfold unpaired; refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hi : separation (Wisps.down S r) (place S i) ≤ Next.SectorChange.span S.patch x
    · rw [clue_zero T k V h r j fun hj => hij (by
        apply (separation_triangle _ (Wisps.down S r) _).trans
        rw [separation_comm (place S i)]; omega),mul_zero]
    rw [clue_zero _ _ _ h r i hi,zero_mul]
  next hx => exact Reaches.one (place S) _ _ _ hij

lemma furnished (h : S.patch.Branches S.kernel G) (A : Stores S) (F : Forest S.ratio)
    (he : Next.SectorChange.span S.patch x ≤ radiusB x/50) :
    Aperture (place S) (radiusB x) (windows S x) (AFull T A F x V k) :=
  ⟨(kernel_reach T k V h x A F).trans (by omega),fun i j hj => (contained i j hj).trans (by omega)⟩
end YM.AnalyticBridge.RelativeLogdet.Physical
