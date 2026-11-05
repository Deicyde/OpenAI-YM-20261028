import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Chosen


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Inactive-position completion is by identity

Show that working just on active is valid even for the panel prescription;
*restrict the same A* before inverse. A notation for full-space computations:
order keys Active-first (e.g. `sorted` below, which really indexes all
positive fine links incl tree/frozen with physical colors). Can simultaneously
permute back on all occurrences if desired. No factor of a Gaussian
link or chart price from inactive tangents. (Group Haar on the frozen
holds is separate.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.Completion
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian Rows
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented 
open Wisps Tier Schur LocalJet
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

section generic
variable {α β σ δ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype δ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq δ]

def wide (A : Gaussian.Table α) (B : Gaussian.Table β) := Matrix.fromBlocks A 0 0 B

lemma wide_mul (A C : Gaussian.Table α) (B D : Gaussian.Table β) :
    wide A B * wide C D = wide (A*C) (B*D) := by unfold wide; rw [Matrix.fromBlocks_multiply]; simp
lemma wide_one : wide (1:Gaussian.Table α) (1:Gaussian.Table β) = 1 := by
  ext (i|i) (j|j) <;> simp [wide,Matrix.one_apply]
lemma wide_det (A : Gaussian.Table α) (B : Gaussian.Table β) : Matrix.det (wide A B)=Matrix.det A * Matrix.det B :=
  Matrix.det_fromBlocks_zero₁₂ ..
lemma wide_inv (A : Gaussian.Table α) (B : Gaussian.Table β) (h : IsUnit A.det) (ht : IsUnit B.det) :
    (wide A B)⁻¹=wide A⁻¹ B⁻¹ := Matrix.inv_eq_right_inv (by rw [wide_mul,A.mul_nonsing_inv h,B.mul_nonsing_inv ht,wide_one])
lemma wide_id_inv (A : Gaussian.Table α) (h : IsUnit A.det) : (wide A (1:Gaussian.Table β))⁻¹=wide A⁻¹ 1 := by
  rw [wide_inv _ _ h (by simp)]; simp

lemma wide_move (A : Gaussian.Table α) (B : Gaussian.Table β) (x : Vec (α⊕β)) :
    wide A B *ᵥ x = Sum.elim (A *ᵥ (x ∘ Sum.inl)) (B *ᵥ (x ∘ Sum.inr)) := by
  rw [wide, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero,zero_add]
lemma wide_cost (A : Gaussian.Table α) (B : Gaussian.Table β) (x : Vec (α⊕β)) :
    let l := x ∘ Sum.inl; let r := x ∘ Sum.inr; x ⬝ᵥ (wide A B *ᵥ x) = l ⬝ᵥ (A *ᵥ l) + r ⬝ᵥ (B *ᵥ r) := by
  rw [wide_move,dotProduct,Fintype.sum_sum_type]; rfl
lemma wide_gap {A : Gaussian.Table α} (hA : Matrix.IsSymm A) {η : ℝ} (h : Gapped A η) :
    let B := wide A (1:Gaussian.Table β)
    B.IsSymm ∧ Gapped B (min η 1) := by
  intro B
  constructor
  · unfold B wide Matrix.IsSymm; ext (i|i) (j|j) <;> simp [Matrix.IsSymm.apply hA,Matrix.one_apply,eq_comm]
  intro u
  rw [show B=_ from rfl,wide_cost]
  rw [one_mulVec]; have he := h (u ∘ Sum.inl)
  rw [← sumSq_dot (u ∘ Sum.inr),sumSq,Fintype.sum_sum_type]
  change min η 1*(sumSq (u ∘ Sum.inl)+sumSq (u ∘ Sum.inr)) ≤ _
  rw [mul_add]; gcongr
  · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (sumSq_nn _)).trans he
  exact mul_le_of_le_one_left (sumSq_nn _) (min_le_right _ _)

-- Relabel any window by its active and ignored portions
private def here (s : Set (α⊕β)) := Sum.inl ⁻¹' s
private def there (s : Set (α⊕β)) := Sum.inr ⁻¹' s
private def divideWindow (s : Set (α⊕β)) : (here s ⊕ there s) ≃ s where
  toFun t := t.elim (fun i => ⟨Sum.inl i.val,i.property⟩) (fun i => ⟨Sum.inr i.val,i.property⟩)
  invFun
    | ⟨.inl x,hx⟩ => .inl ⟨x,hx⟩
    | ⟨.inr x,hx⟩ => .inr ⟨x,hx⟩
  left_inv := by intro t; cases t <;> rfl
  right_inv := by rintro ⟨i|i,h⟩ <;> rfl

lemma e_inv (A B : Gaussian.Table σ) (e : δ ≃ σ) (hA : IsUnit A.det)
    (h : A * B=1) : (A.submatrix e e)⁻¹=B.submatrix e e := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.submatrix_mul_equiv,h]; ext i j
  simp [Matrix.one_apply]

lemma sub_inv (A : Gaussian.Table σ) (e : δ ≃ σ) (hA : IsUnit A.det) :
    (A.submatrix e e)⁻¹=A⁻¹.submatrix e e := e_inv A A⁻¹ e hA (A.mul_nonsing_inv hA)

lemma window_inv (A : Gaussian.Table α) (s : Set (α⊕β)) {η : ℝ} (h : Gapped A η) (hA : A.IsSymm) (hη : 0 < η) :
    ((principal (wide A 1) s)⁻¹.submatrix (divideWindow s) (divideWindow s)) = wide (principal A (here s))⁻¹ 1 := by
  let p := principal (wide A (1:Gaussian.Table β)) s
  let H := principal A (here s)
  have he : p.IsSymm := (wide_gap hA h (β:=β)).1.submatrix _
  have ht := held_gap (wide_gap hA h (β:=β)).2 s
  let e := divideWindow s
  have hp : p.submatrix e e = wide H 1 := by
    ext (i|i) (j|j) <;> first | rfl | skip
    -- key β
    change (1:Gaussian.Table β) i.val j.val = (1 : Gaussian.Table (there s)) i j
    simp [Matrix.one_apply,Subtype.val_inj]
  change p⁻¹.submatrix e e=wide H⁻¹ _
  rw [← sub_inv _ _ (handles ht he (lt_min hη (by norm_num))), hp, wide_id_inv H (handles (held_gap h _) (hA.submatrix _) hη)]

private def small (W : α⊕β → Set (α⊕β)) (i : α) := here (W (.inl i))
lemma stamp (A : Gaussian.Table α) (W : α⊕β → Set (α⊕β))
    {η : ℝ} (h : Gapped A η) (hA : A.IsSymm) (hη : 0 < η) (hw : ∀ i, i∈W i) :
    Schur.per W (wide A 1) = wide (Schur.per (small W) A) 1 := by
  let Z := wide A (1:Gaussian.Table β)
  let e (p : α ⊕ β) := divideWindow (W p)
  have he i : ((principal Z (W i))⁻¹).submatrix (e i) (e i)= _ := window_inv A (W i) h hA hη
  ext (j|j) (i|i)
  · have hs : i∈small W i := hw (.inl i)
    change Schur.per W Z (.inl j) (.inl i)=Schur.per (small W) A j i
    by_cases hx : j ∈ small W i
    · let v : here (W (Sum.inl i)) := ⟨j,hx⟩
      let u : here (W (Sum.inl i)) := ⟨i,hs⟩
      rw [per_read W _ (hw (.inl i)) hx,per_read _ _ hs hx]
      exact congr_fun (congr_fun (he (.inl i)) (.inl v)) (.inl u)
    exact (per_zero W _ hx).trans (per_zero _ _ hx).symm
  · let v : there (W (Sum.inr i)) := ⟨i,hw (.inr i)⟩
    change Schur.per W Z (.inl j) (.inr i)=0
    by_cases hx : Sum.inl j ∈ W (.inr i)
    · rw [per_read W _ (hw _) hx]
      exact congr_fun (congr_fun (he (.inr i)) (.inl (show here (W (.inr i)) from ⟨j,hx⟩))) (.inr v)
    exact per_zero W _ hx
  · let u : here (W (Sum.inl i)) := ⟨i, hw (.inl i)⟩
    change Schur.per W Z (.inr j) (.inl i)=0
    by_cases hx : Sum.inr j ∈ W (.inl i)
    · rw [per_read W _ (hw _) hx]
      exact congr_fun (congr_fun (he (.inl i)) (.inr (show there (W (.inl i)) from ⟨j,hx⟩))) (.inl u)
    exact per_zero W _ hx
  let u : there (W (Sum.inr i)) := ⟨i, hw (.inr i)⟩
  change Schur.per W Z (.inr j) (.inr i)=(1 : Gaussian.Table β) j i
  by_cases hx : Sum.inr j ∈ W (.inr i)
  · let v : there (W (Sum.inr i)) := ⟨j,hx⟩
    rw [per_read W _ (hw _) hx]
    refine (congr_fun (congr_fun (he (.inr i)) (.inr v)) (.inr u)).trans ?_
    change (1 : Gaussian.Table (there (W (.inr i)))) v u = _
    rw [Matrix.one_apply,Matrix.one_apply]; split
    next h => rw [if_pos (show j=i from congr_arg Subtype.val h)]
    next h => rw [if_neg (show j≠i from fun e => h (Subtype.ext e))]
  rw [per_zero W _ hx,Matrix.one_apply,if_neg (fun h => hx (by rw [h]; exact hw _))]

lemma wide_cloud (A : Gaussian.Table α) (W : α⊕β → Set (α⊕β)) {η : ℝ} (h : Gapped A η) (hA : A.IsSymm) (hη : 0 < η) (hw : ∀ i, i∈W i) :
    clouded W (wide A 1)=wide (clouded (small W) A) 1 := by
  unfold clouded; rw [stamp _ _ h hA hη hw]; ext (i|i) (j|j) <;> first | rfl | simp [wide,Matrix.one_apply,eq_comm]
  split <;> norm_num
end generic

variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ} (A : Stores S) (F : Forest S.ratio)

abbrev fundEdge (i : Active A x F) : Bond f := i.val.val
lemma fund_inj (G : Gauge) (x) : Function.Injective (fundEdge A F (x:=x)) := fun i j h => Subtype.ext (Subtype.ext h)
private abbrev supportTest (A : Stores S) (F : Forest S.ratio) (x) (i : Bond f × G.ColorIndex) :=
    ∃ j : Active A x F × G.ColorIndex,i=(fundEdge A F j.1,j.2)
abbrev reserved (x : ℝ) (G : Gauge) := Subtype (supportTest A F x (G:=G))
abbrev vacant (x : ℝ) (G : Gauge) := Subtype (fun i => ¬supportTest A F x (G:=G) i)

scoped instance (x : ℝ) (G : Gauge) : Fintype (vacant A F x G) := Fintype.ofFinite _
private def holder : In x A F (G:=G) ≃ reserved A F x G :=
  Equiv.ofBijective (fun i : In x A F (G:=G) => (⟨(fundEdge A F i.1,i.2),i,rfl⟩ : reserved A F x G))
    ⟨fun i j h => by
        have he := congr_arg Subtype.val h
        apply Prod.ext
        · apply fund_inj A F G x; exact congr_arg Prod.fst he
        · exact congr_arg (fun i : Bond f × G.ColorIndex => i.2) he,
      fun ⟨i,j,h⟩ => ⟨j,Subtype.ext h.symm⟩⟩

def sorted : (In x A F (G:=G) ⊕ vacant A F x G) ≃ Bond f × G.ColorIndex :=
    ((holder A F).sumCongr (Equiv.refl _)).trans (Equiv.sumCompl (supportTest A F x))
lemma sorted_first (i : In x A F (G:=G)) : sorted A F (.inl i)=(fundEdge A F i.1,i.2) := rfl
lemma sorted_last (i : vacant A F x G) : sorted A F (.inr i)=i.val := rfl

def allPanels (i : In x A F (G:=G) ⊕ vacant A F x G) := {j : In x A F (G:=G) ⊕ vacant A F x G | meeting S x (sorted A F i).1 (sorted A F j).1}

lemma well_cut (i : In x A F (G:=G)) : panels A F i = small (allPanels A F) i := rfl

/-- On the identity completion with the same windows (also for whole
unused link blocks!), the literal construction gives just the identity
completion of the integral's covariance. Thus not omitting any
propagating zero modes even if integrating in this convention. -/
lemma stocked (x : ℝ) (T : Tube G S) (k : S.Choices) (V : Config G c) {η} (hη : 0<η)
    (h : Gapped (Rows.gram T x V k (shots S x) A F) η) (hb : 120≤radiusB x) :
    let Q := Rows.gram T x V k (shots S x) A F
    let W := Schur.per (panels A F) Q
    let U := Schur.per (allPanels A F) (wide Q 1)
    U = wide W 1 ∧ clouded (allPanels A F) (wide Q 1) = wide (fog A F T x V k) 1 ∧
      (wide Q (1:Gaussian.Table (vacant A F x G))).det = Q.det ∧
      ∀ (u : Vec (In x A F (G:=G))), -U.transpose *ᵥ (Sum.elim u (0 : Vec (vacant A F x G))) =
        Sum.elim (-W.transpose *ᵥ u) 0 := by
  intro Q M N
  have hw i : i ∈ allPanels A F (x:=x) (G:=G) i := by
    intro y hy z hz
    set n := S.ratio.parent (sorted A F i).1.1
    have he : separation y n ≤ 1 := (separation_comm ..).trans_le (meetings _ hy)
    have hr : separation n z ≤ 1 := meetings _ hz
    apply (separation_triangle y n z).trans; omega
  have hQ : Q.IsSymm := by unfold Q Rows.gram Matrix.IsSymm; rw [Matrix.transpose_mul,Matrix.transpose_transpose]
  let E := allPanels A F (x:=x) (G:=G)
  have h₀ : small E = panels A F := funext fun i => (well_cut _ _ _).symm
  have hz := stamp Q E h hQ hη hw
  rw [h₀] at hz
  have ht : N=wide M 1 := by
    unfold N M
    convert hz using 2 -- expose
  refine ⟨ht,?_,?_, fun u => ?_⟩
  · have hi := wide_cloud Q E h hQ hη hw; rw [h₀] at hi; unfold fog; convert hi using 2
  · have hx := wide_det Q (1:Gaussian.Table (vacant A F x G)); rw [Matrix.det_one,mul_one] at hx
    convert hx using 2
  rw [ht, Matrix.neg_mulVec, Matrix.neg_mulVec,wide,Matrix.fromBlocks_transpose]
  simp_rw [transpose_zero,transpose_one]
  change -(wide M.transpose (1:Gaussian.Table _) *ᵥ _) = _
  rw [wide_move,one_mulVec]; ext (i|i) <;> first | rfl | simp [Function.comp]
end YM.Next.SectorChange.Completion
