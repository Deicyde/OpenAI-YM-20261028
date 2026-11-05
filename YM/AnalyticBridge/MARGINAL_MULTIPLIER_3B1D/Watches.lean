import YM.AnalyticBridge.MARGINAL_MULTIPLIER_3B1D.Meters

/-!
# Enclose the actual same-Gram matrix and window calculations

No proof of derivative existence used here for raw switched V formulas.
All entire principal matrices and boundary-row stencil tests compared
before inverse, for this step's actual active-address fog prescription.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
open Function Filter Set Lattice RG Wilson Next.SectorChange Pressure Pressure.Tube Pressure.Stores
  Push.SectorMeasure Precision Tree Matrix Next.SectorChange.Schur Next.SectorChange.Wisps Next.SectorChange.Tier
  Next.SectorChange.LocalJet Next.SectorChange.Rows Next.Fluctuations Bid FiniteMatrix Gaussian Exterior
open scoped Topology BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A A' : Stores S} {F F' : Forest S.ratio} {V V' : Config G c} {x : ℝ} {k k' : S.Choices} {o : Site c} {r : ℕ}
    {Y : LinkArray G (Frozen A x F)} {Y' : LinkArray G (Frozen A' x F')}
    {i j : Rows.In x A F (G:=G)} {i' j' : Rows.In x A' F' (G:=G)}
lemma faces {x' : ℝ} {i' : Rows.In x' A' F' (G:=G)} (hi : lift i=lift i') : front A F i = front A' F' i' := congr_arg (fun e : Full S G => S.ratio.parent e.1.1) hi

lemma gram_eq (hs : S.patch.Branches S.kernel G) (h : Scan S x (front A F i) (2*span S.patch x) A A' F F' k k' V V' Y Y')
    (hi : lift i=lift i') (hj : lift j=lift j') : Rows.gram T x V k (shots S x) A F i j=Rows.gram T x V' k' (shots S x) A' F' i' j' := by
  rw [Rows.gram,Rows.gram,Matrix.mul_apply,Matrix.mul_apply]; refine Finset.sum_congr rfl fun u _ => ?_
  simp only [Matrix.transpose_apply]; by_cases he : span S.patch x < separation (down S u) (front A F i)
  · rw [move_range hs he,move_range hs (i:=u) (j:=i') (by rwa [← faces hi]),zero_mul,zero_mul]
  have hu := h.shrink (u:=down S u) (r':=span S.patch x) (by rw [separation_comm]; omega)
  rw [move_eq hs hu hi,move_eq hs hu hj]

section panels
local notation "L" => panels A F (x:=x) (G:=G)
local notation "R" => panels A' F' (x:=x) (G:=G)
lemma ball_member (he : j ∈ L i) : separation (front A F i) (front A F j) ≤ radiusB x/20 := he _ (by simp [Next.SectorChange.points,front]) _ (by simp [Next.SectorChange.points,front])
private lemma select_same (hi : lift i=lift i') (hj : lift j=lift j') : j∈L i ↔ j'∈R i' := by change meeting _ _ _ _ ↔ meeting _ _ _ _; rw [show i.1.val.val=i'.1.val.val from congr_arg Prod.fst hi, show j.1.val.val=j'.1.val.val from congr_arg Prod.fst hj]
private def leftField (h : Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') (j : L i) : R i' := by
  let e := (h.switch j.val.1 (ball_member j.property)).choose
  let j' := (e,j.val.2)
  have hj : lift j.val=lift j' := Prod.ext (h.switch j.val.1 (ball_member j.property)).choose_spec rfl
  exact ⟨j',(select_same hi hj).mp j.property⟩
private lemma left_spec (h : Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') (j : L i) : lift j.val=lift (leftField h hi j).val := Prod.ext (h.switch j.val.1 (ball_member j.property)).choose_spec rfl
private def window (h : Scan S x (front A F i) (radiusB x/20) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') : L i ≃ R i' where
  toFun := leftField h hi
  invFun := leftField ((faces hi) ▸ h.turn) hi.symm
  left_inv j := Subtype.ext ((lifting_injective ..) ((left_spec _ _ j).trans (left_spec ..)).symm)
  right_inv j := Subtype.ext ((lifting_injective ..) ((left_spec _ _ j).trans (left_spec ..)).symm)
private lemma synced {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {W : α → Set α} {W' : β → Set β}
    (M : Gaussian.Table α) (N : Gaussian.Table β) {i j : α} {i' j' : β} (hi : i ∈ W j) (hj : j ∈ W j) (hi' : i' ∈ W' j') (hj' : j' ∈ W' j')
    (e : W j ≃ W' j') (he : principal M (W j) = (principal N (W' j')).submatrix e e) (hx : (e ⟨i,hi⟩).val=i') (hv : (e ⟨j,hj⟩).val=j') : Schur.per W M i j=Schur.per W' N i' j' := by
  rw [per_read _ _ hj hi, per_read _ _ hj' hi',he,Matrix.inv_submatrix_equiv,Matrix.submatrix_apply,show e ⟨i,hi⟩=⟨i',hi'⟩ from Subtype.ext hx,show e ⟨j,hj⟩=⟨j',hj'⟩ from Subtype.ext hv]
lemma per_eq (hr : Ready T x) (h : Scan S x (front A F i) (radiusB x/10) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') (hj : lift j=lift j') :
    Schur.per L (Rows.gram T x V k (shots S x) A F) j i=Schur.per R (Rows.gram T x V' k' (shots S x) A' F') j' i' := by
  have hx : i∈L i := per_self (boards A F G hr.length) i
  let H := h.lower (r':=radiusB x/20) (by omega)
  let e := window H hi
  let M := principal (Rows.gram T x V k (shots S x) A F) (L i)
  let N := principal (Rows.gram T x V' k' (shots S x) A' F') (R i')
  have he : M=N.submatrix e e := by
    ext a b
    have ha := ball_member a.property
    exact gram_eq hr.rules (i:=a.val) (j:=b.val) (h.shrink (by have := hr.inputs; omega)) (left_spec H hi a) (left_spec H hi b)
  have hh u (j : L i) (hv : lift j.val=lift u) : (e j).val=u := (lifting_injective ..) ((left_spec H hi j).symm.trans hv)
  by_cases hv : j∈L i
  · exact synced _ _ hv hx ((select_same hi hj).1 hv) ((select_same hi hi).1 hx) e he (hh _ ⟨j,hv⟩ hj) (hh _ ⟨i,hx⟩ hi)
  rw [per_zero _ _ hv,per_zero _ _ (mt (select_same hi hj).mpr hv)]
lemma fog_eq (hr : Ready T x) (h : Scan S x (front A F i) (radiusB x/5) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') (hj : lift j=lift j') :
    fog A F T x V k i j=fog A' F' T x V' k' i' j' := by
  by_cases hv : j∈L i
  · unfold fog clouded; simp only [Matrix.transpose_apply,Matrix.smul_apply,Matrix.add_apply]
    rw [per_eq hr (h.lower (by omega)) hi hj, per_eq hr (h.shrink (by have := ball_member hv; omega)) hj hi]
  rw [fog_zero _ _ _ _ _ _ _ _ hv,fog_zero _ _ _ _ _ _ _ _ (mt (select_same hi hj).mpr hv)]
end panels

private def fill {ι : Type} (φ : ι → ℝ) (e : ι → Full S G) (j : Full S G) :=
    if h : j∈Set.range e then φ h.choose else 0
private lemma fill_at {ι : Type} (φ : ι → ℝ) (e : ι → Full S G) (he : Injective e) (j : ι) : fill φ e (e j) = φ j := by
  unfold fill; rw [dif_pos (mem_range_self _)]; exact congr_arg φ (he ((show e j ∈ Set.range e from mem_range_self ..).choose_spec))
private lemma fill_sum {ι : Type} [Fintype ι] (φ : ι → ℝ) (e : ι → Full S G) (he : Injective e) :
    ∑ i, φ i = ∑ i, fill φ e i := by
  let E : ι ↪ Full S G := ⟨e,he⟩
  calc
    _ = ∑ i∈Finset.univ.map E, fill φ e i := by rw [Finset.sum_map]; exact Finset.sum_congr rfl fun j _ => (fill_at φ e he j).symm
    _ = _ := Finset.sum_subset (Finset.subset_univ _) fun j _ hj => dif_neg (fun ⟨i,hi⟩ => hj (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hi⟩))
lemma sum_eq (h : Scan S x o r A A' F F' k k' V V' Y Y') {a : Prices G (Active A x F)} {b : Prices G (Active A' x F')}
    (hl : ∀ i, r < separation o (front A F i) → a i=0) (hr : ∀ i, r < separation o (front A' F' i) → b i=0)
    (he : ∀ i j, separation o (front A F i) ≤ r → lift i=lift j → a i=b j) : ∑ i,a i=∑ j,b j := by
  let w := lift (F:=F) (x:=x) (A:=A) (G:=G); let z := lift (F:=F') (x:=x) (A:=A') (G:=G)
  have hw : Injective w := lifting_injective ..; have hz : Injective z := lifting_injective ..
  rw [fill_sum a w hw, fill_sum b z hz]; refine Finset.sum_congr rfl fun u _ => ?_
  unfold fill; split <;> split
  · rename_i h₁ h₂
    have hu := h₁.choose_spec.trans h₂.choose_spec.symm
    by_cases hQ : separation o (S.ratio.parent u.1.1) ≤ r
    · rw [← h₁.choose_spec] at hQ; exact he _ _ hQ hu
    have hQ := lt_of_not_ge hQ
    rw [hl _ (by rw [← h₁.choose_spec] at hQ; exact hQ), hr _ (by rw [← h₂.choose_spec] at hQ; exact hQ)]
  · rename_i h₁ h₂
    apply hl; apply lt_of_not_ge; intro hi
    obtain ⟨p,hp⟩ := h.switch h₁.choose.1 hi
    exact h₂ ⟨(p,h₁.choose.2), (show z (p,h₁.choose.2)=w h₁.choose from Prod.ext hp.symm rfl).trans h₁.choose_spec⟩
  · symm; rename_i h₁ h₂; apply hr; apply lt_of_not_ge; intro hi
    obtain ⟨p,hp⟩ := h.turn.switch h₂.choose.1 hi
    exact h₁ ⟨(p,h₂.choose.2), (show w (p,h₂.choose.2)=z h₂.choose from Prod.ext hp.symm rfl).trans h₂.choose_spec⟩
  rfl
variable {q : Chi} {β d : ℝ}
lemma blame_eq (hr : Ready T x) (h : Scan S x (front A F i) (radiusB x/5) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') :
    blame T x V k (shots S x) A F q d Y i = blame T x V' k' (shots S x) A' F' q d Y' i' := by
  unfold blame mulVec dotProduct; simp only [Matrix.transpose_apply]; refine Finset.sum_congr rfl fun j _ => ?_
  have hs := hr.inputs
  by_cases hh : span S.patch x < separation (down S j) (front A F i)
  · rw [move_range hr.rules hh,move_range hr.rules (i:=j) (j:=i') (by rwa [← faces hi]),zero_mul,zero_mul]
  rw [move_eq hr.rules (i:=j) (h.shrink (by rw [separation_comm]; omega)) hi,
      source_eq hr (i:=j) (h.shrink (by rw [separation_comm]; omega))]
lemma mean_eq (hr : Ready T x) (h : Scan S x (front A F i) (radiusB x/3) A A' F F' k k' V V' Y Y') (hi : lift i=lift i') :
    meanLog A F T x V k q d Y i = meanLog A' F' T x V' k' q d Y' i' := by
  unfold meanLog mulVec dotProduct; simp only [Matrix.neg_apply, Matrix.transpose_apply]
  refine sum_eq (h.lower (r':=radiusB x/20) (by omega)) (fun j hj => ?_) (fun j hj => ?_) fun j j' hj hh => ?_
  · rw [per_zero (panels A F) _ (i:=i) (j:=j) (fun he => hj.not_ge (ball_member he)),neg_zero,zero_mul]
  · rw [per_zero (panels A' F') _ (i:=i') (j:=j) (fun he => hj.not_ge (?_ : _ ≤ _)),neg_zero,zero_mul]; exact (faces hi).symm ▸ ball_member he
  rw [blame_eq hr (i:=j) (h.shrink (by omega)) hh,per_eq hr (h.lower (by omega)) hi hh]


end YM.AnalyticBridge.MarginalMultiplier3b1d.PatchReads
