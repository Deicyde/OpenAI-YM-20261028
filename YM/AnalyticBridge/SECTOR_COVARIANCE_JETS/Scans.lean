import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.District

set_option warningAsError false

/-!
# Exact support comparisons at fixed x, even on field or tag perturbation

This is lookup before unassigned/likelihood regrouping; charged BOTH ends,
and enough everywhere even if windows overlap or wrap. Does not transfer a
price/jet to a table violating its V-flag hypotheses. Housed comparisons
use only values on that full table. -/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Terrain
open Function Filter Lattice RG RG.Patch Wilson Pressure Pressure.Tube Pressure.Stores Precision Exterior Bloch Tree Matrix Finset
open YM.Push.SectorMeasure YM.Next.Fluctuations YM.Next.SectorChange Motion Metric Oriented LocalJet Schur
open Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Completion
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x u : ℝ}
variable {V V' : Config G c} {F F' : Forest S.ratio} {A A' : Stores S} {t t' : S.Choices}

def home (S : StepData c f) (i : Atom G f) := S.ratio.parent i.1.1

lemma bump_closed {i : Twin f} (T : Tube G S) (s : Signed) (a : Directions G f) (x : ℝ) :
    Housed (E:=G.El) (s.act (S.ratio.parent i.1.1)) (span S.patch x) (fun V => faceKick T x V a s i) := by
  intro U V h; unfold faceKick; split
  · apply tsum_congr; intro j; dsimp only; split
    · let p := (T.up.row i.1.2 j).2
      have hp : p.length ≤ till x := by assumption
      have hv : strand S s a i.1.1 p U=strand S s a i.1.1 p V := strand_houses _ _ _ _ _ _ _ (fun i hi => h i (hi.trans (by unfold span; omega)))
      exact congr_arg (fun z : G.Color => (T.up.row i.1.2 j).1 • z) hv
    rfl
  apply congr_arg; apply face_houses
  intro i hi; exact h _ (hi.trans (by unfold span; omega))

private lemma count_row (W : Config G c) (A : Stores S) (F : Forest S.ratio) (t : S.Choices)
    (T : Tube G S) (x : ℝ) (i : Receipt G S) (j : Atom G f) :
    scanD T A F t x W i j = if onStage A F x j.1 ∧ keep x (shots S x) A F i.1 then
      componentG i.2 (slip • (bump T x W t (atom j) i.1)) else 0 := by
  unfold scanD; rw [Matrix.of_apply]
  by_cases h : onStage A F x j.1
  · rw [if_pos h]; change _=if _ then _ else _
    obtain ⟨i,i'⟩ := i; rw [tape_read]; unfold Rows.selected Rows.restrict
    by_cases hk : keep x (shots S x) A F i
    · rw [if_pos hk, if_pos (And.intro h hk)]; rfl
    rw [if_neg hk,if_neg (fun h => hk h.2)]; rfl
  rw [if_neg h, if_neg (fun he => h he.1)]

lemma avoids_D (S : StepData c f) (hS : S.patch.Branches S.kernel G)
    (i : Receipt G S) (j : Atom G f) (V : Config G c) (t : S.Choices) (A : Stores S) (F : Forest S.ratio) (T : Tube G S)
    (x : ℝ) (h : ¬separation (down S i) (home S j) ≤ span S.patch x) : scanD T A F t x V i j=0 := by
  rw [count_row]; split; swap; · rfl
  let a := (i.1.2).elim (fun p => Sum.inl p.1) Sum.inr
  have hv : bump T x V t (atom j) i.1 = bump T x V t 0 i.1 := by
    apply bump_dep T x V t i.1.1 i.1.2 _ _ hS
    intro e he; unfold atom; rw [on_axis]; have hi : e ≠ j.1 := by
      intro ha; apply h; subst e; exact (contains ..).1 he
    rw [Pi.single_eq_of_ne hi]; rfl
  rw [hv]
  obtain ⟨⟨s,b|b⟩,i⟩ := i
  · simp [bump,faceKick, barrel]
  simp [bump,noiseKick]

def round (P : Patch) (x : ℝ) := span P x+10*radiusB x+8

lemma curb_together {s : Signed} {i : Where S} (h : Teams S (s.act (roots S i)) (span S.patch x) (round S.patch x) F F' A A' t t' V V') :
    curb (shots S x) A F x s i ↔ curb (shots S x) A' F' x s i := by
  have hv (A : Stores S) (F : Forest S.ratio) : curb (shots S x) A F x s i ↔
      ∃ e : Bond f,e∈shots S x s i ∧ onStage A F x e := by
    simp only [acts_here,curb]; constructor
    · rintro ⟨j,hj⟩; exact ⟨_,hj,j,rfl⟩
    rintro ⟨e,he,j,hj⟩; exact ⟨j,hj.symm ▸ he⟩
  rw [hv,hv]; apply exists_congr
  intro e; by_cases he : e∈shots S x s i
  · have hk := (contains ..).mp he
    rw [h.curtain (by unfold round; omega)]
  simp only [he,false_and]

private lemma equal_prediction (U : Config G f) (s : Signed) (i : Bond c)
    (h : (choice (S:=S) s t).1 i.1 = (choice s t').1 i.1)
    (ht : (choice (S:=S) s t).1 (i.1+step i.2) = (choice s t').1 (i.1+step i.2))
    (hh : (choice (S:=S) s t).2 i=(choice s t').2 i) :
    S.prediction U (choice s t) i=S.prediction U (choice s t') i := by
  unfold StepData.prediction StepData.connector StepData.frames; simp_rw [hh,h,ht]

lemma D_seen (T : Tube G S) (i : Receipt G S) (j : Atom G f) (hS : S.patch.Branches S.kernel G)
    (h : Teams S (down S i) (span S.patch x) (round S.patch x) F F' A A' t t' V V') : scanD T A F t x V i j=scanD T A' F' t' x V' i j := by
  let K := span S.patch x; let r := round S.patch x
  by_cases he : separation (down S i) (home S j) ≤ K
  swap
  · exact (avoids_D S hS i j _ _ _ _ T x he).trans (avoids_D S hS i j _ _ _ _ T x he).symm
  rw [count_row, count_row]
  have ht : onStage A F x j.1 ↔ onStage A' F' x j.1 := by
    apply h.curtain; unfold round; unfold K home at he; omega
  have hv : keep x (shots S x) A F i.1 ↔ keep x (shots S x) A' F' i.1 := by
    cases hi : i with
    | mk b j =>
      rcases b with ⟨s,b|b⟩ <;> subst i
      · exact curb_together (i:=.inl b.1) h
      exact curb_together (i:=.inr b) h
  rw [ht,hv]; split; swap; · rfl
  have hf : bump T x V t (atom j) i.1=bump T x V' t' (atom j) i.1 := by
    rcases i with ⟨⟨s,b|b⟩,i⟩
    · exact bump_closed T s _ x V V' h.signal
    change noiseKick V t _ s b=noiseKick V' t' _ s b; unfold noiseKick
    have hv := block_houses S t s b (atom j) hS V V' (fun i hi => h.signal i (hi.trans (by unfold span; omega)))
    dsimp only at hv; rw [hv]
    have hh : predictorTurn V' t s b=predictorTurn V' t' s b := by
      obtain ⟨h1,h2,h3⟩ := h.votes (s:=s) (i:=b) (by change separation (s.act b.1) _ + _ ≤ _; rw [separation_self]; unfold round; omega)
      funext a; unfold predictorTurn predictGroup
      simp_rw [equal_prediction (S:=S) _ s b h1 h2 h3]
    unfold blockJet; simp_rw [hh]
  rw [hf]

def lengthA (P : Patch) (x : ℝ) := 2*span P x
def roundA (P : Patch) (x : ℝ) := span P x+round P x
lemma seenA (T : Tube G S) (i j : Atom G f) (hS : S.patch.Branches S.kernel G)
    (h : Teams S (home S i) (lengthA S.patch x) (roundA S.patch x) F F' A A' t t' V V') : scanA T A F t x V i j=scanA T A' F' t' x V' i j := by
  unfold scanA; rw [Matrix.add_apply,Matrix.add_apply]; apply congr_arg₂
  · simp only [Matrix.mul_apply,Matrix.transpose_apply]; apply sum_congr rfl; intro b _
    by_cases he : separation (down S b) (home S i) ≤ span S.patch x
    · rw [separation_comm] at he
      have hh := h.zone (p:=down S b) (show separation (home S i) _+span S.patch x ≤ lengthA S.patch x by unfold lengthA; omega) (s:=round S.patch x) (by unfold roundA; omega)
      rw [D_seen T b i hS hh,D_seen T b j hS hh]
    rw [avoids_D _ hS _ _ _ _ _ _ _ _ he, avoids_D _ hS _ _ _ _ _ _ _ _ he,zero_mul,zero_mul]
  by_cases hi : i=j
  · subst j; rw [shard,shard,diagonal_apply_eq,diagonal_apply_eq]
    rw [h.curtain (by unfold roundA round home; rw [separation_self]; omega)]
  unfold shard; rw [diagonal_apply_ne _ hi,diagonal_apply_ne _ hi]

lemma absentA (T : Tube G S) (i j : Atom G f) (hS : S.patch.Branches S.kernel G) (A : Stores S) (x : ℝ) (V : Config G c) (t : S.Choices) (F : Forest S.ratio)
    (h : ¬ separation (home S i) (home S j) ≤ lengthA S.patch x) : scanA T A F t x V i j=0 := by
  unfold scanA; rw [Matrix.add_apply,shard,diagonal_apply_ne _ (show i≠j from fun he => h (by rw [he,separation_self]; omega)),add_zero,Matrix.mul_apply]
  apply sum_eq_zero; intro b _
  by_cases he : separation (down S b) (home S i) ≤ span S.patch x
  · have hk : ¬ separation (down S b) (home S j) ≤ span S.patch x := by
      intro ho; apply h
      apply (separation_triangle _ (down S b) _).trans
      rw [separation_comm _ (down S b)]; unfold lengthA; omega
    rw [avoids_D S hS b j _ _ _ _ _ _ hk,mul_zero]
  rw [Matrix.transpose_apply,avoids_D S hS b i _ _ _ _ _ _ he,zero_mul]
end YM.AnalyticBridge.Covariance.Terrain
