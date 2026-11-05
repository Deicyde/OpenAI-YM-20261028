import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Potential stencils for the a coefficients, one allowed selection

Overcounts using site balls of output radius R+4+predReach+1 (fine R,
slack for reversal shift). Can truncate much sharper; this is still
within B/50 in output units after delay. Counts all paths witnessing a
cut row, no sparsification by value. Authentic predictor branch stencils. Lemmas even before smallness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
open YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure
open YM.Next.Fluctuations YM.Next.Fluctuations.Sector YM.Push.SectorMeasure.Oriented
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

def span (P : Patch) (x : ℝ) := till x + 5 + predReach P

def roots (S : StepData c f) (i : Where S) : Site c := i.elim (fun p => S.ratio.parent p.1) (Prod.fst)

def shots (S : StepData c f) (x : ℝ) : Stencils S := fun s i => Finset.univ.filter fun e =>
  separation (s.act (roots S i)) (S.ratio.parent e.1) ≤ span S.patch x

lemma contains (s : Signed) (i : Where S) (e : Bond f) : e ∈ shots S x s i ↔
    separation (s.act (roots S i)) (S.ratio.parent e.1) ≤ span S.patch x := Finset.mem_filter.trans (by simp)

lemma spin_separation (e : Bond f) (s : Signed) (o : Site c) :
    separation (s.act o) (S.ratio.parent (sendEdge s 0 e).1) ≤ separation o (S.ratio.parent e.1) + 1 := by
  calc
    _ ≤ separation (s.act o) (s.act (S.ratio.parent e.1)) + separation (s.act (S.ratio.parent e.1))
        (S.ratio.parent (sendEdge s 0 e).1) := separation_triangle ..
    _ ≤ _ := by
        rw [separation_signed, ← Ratio.parent_signed S.ratio S.patch.odd_side]
        refine Nat.add_le_add_left ?_ _
        unfold sendEdge Step.used; split
        · have ht := Work.E03.parent_step S ((s.act e.1)-step (s.perm e.2)) (s.perm e.2)
          simp only [affine,add_zero,Step.rotate,posDir]
          rw [sub_add_cancel, separation_comm] at ht; exact ht
        · simp only [affine,add_zero,separation_self]; omega

lemma pulled_near (U V : Config G f) (s : Signed) (i : Site c) (r : ℕ)
    (h : AgreeNear S.ratio.parent (s.act i) (r+1) U V) :
    AgreeNear S.ratio.parent i r (pull s 0 U) (pull s 0 V) := by
  intro e he
  have hv := h (sendEdge s 0 e) ((spin_separation _ _ _).trans (Nat.add_le_add_right he _))
  unfold pull Step.read; unfold sendEdge at hv; split <;> rw [hv]

lemma slot_distance (P : Slot) (i : Site f) :
    separation (S.ratio.parent i) (S.ratio.parent (Work.F03.slotFace P i).1) ≤ P.walk.length := by
  have he := Work.E03.sep_walk S.ratio.parent (Work.E03.parent_step S) i P.walk
  rw [show (Work.F03.slotFace P i).1 = stop i P.walk from ?_]; exact he
  unfold Work.F03.slotFace Slot.offset; rw [wrap_stop_cover, map_zero,add_comm]
  nth_rw 2 [show i=i+0 by rw [add_zero]]; rw [Work.E03.stop_add_left]

def echo {α : Type} (S : StepData c f) (o : Site c) (R : ℕ) (a b : Bond f → α) :=
  ∀ i : Bond f, separation o (S.ratio.parent i.1) ≤ R → a i=b i

def sourceFace (V : Config G c) (s : Signed) (p : Cell f) (a : Directions G f) :=
  G.curvature (faceValue (facade S s V a) p)

lemma face_dep (V : Config G c) (s : Signed) (p : Cell f) (a b : Directions G f)
    (h : echo S (s.act (S.ratio.parent p.1)) 5 a b) :
    sourceFace (S:=S) V s p a = sourceFace (S:=S) V s p b := by
  unfold sourceFace; congr 1
  refine travel_near _ (Work.E03.parent_step S) _ _ _ _ 4 le_rfl
    (pulled_near _ _ s _ 4 ?_)
  intro i hi; unfold increment; rw [h i hi]

lemma noise_dep (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) (a b : Directions G f)
    (hp : S.patch.Branches S.kernel G)
    (h : echo S (s.act i.1) (predReach S.patch+1) a b) :
    predictGroup V k s i a = predictGroup V k s i b := by
  apply prediction_near_eq hp
  apply pulled_near
  intro i hi; unfold increment; rw [h i hi]

private lemma side_local {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (f : E → H) (a b : E)
    (h : ∀ t : ℝ, f (t • a)=f (t • b)) : fderiv ℝ f 0 a=fderiv ℝ f 0 b := by
  by_cases he : DifferentiableAt ℝ f 0
  · have ht := YM.Push.side f he a; simp_rw [h] at ht
    exact ht.unique (YM.Push.side f he b)
  rw [fderiv_zero_of_not_differentiableAt he]; simp

lemma faceJet_dep (V : Config G c) (s : Signed) (p : Cell f) (a b : Directions G f)
    (h : echo S (s.act (S.ratio.parent p.1)) 5 a b) :
    plaquetteJet S V s p a = plaquetteJet S V s p b := by
  apply side_local (sourceFace V s p)
  exact fun t => face_dep V s p _ _ (fun i hi => congr_arg (fun x : G.Color => t • x) (h i hi))

lemma blockJet_dep (V : Config G c) (k : S.Choices) (s : Signed) (i : Bond c) (a b : Directions G f)
    (hp : S.patch.Branches S.kernel G)
    (h : echo S (s.act i.1) (predReach S.patch+1) a b) :
    blockJet V k s i a = blockJet V k s i b := by
  apply side_local _ a b
  intro t
  dsimp only [predictorTurn]
  rw [noise_dep V k s i (t • a) (t • b) hp (fun i hi => congr_arg (fun x : G.Color => t • x) (h i hi))]

open Rows in
lemma bump_dep (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (s : Signed)
    (j : Twin f ⊕ Bond c) (a b : Directions G f)
    (hp : S.patch.Branches S.kernel G)
    (h : ∀ e ∈ shots S x s (j.elim (fun x => .inl x.1) Sum.inr), a e=b e) :
    bump T x V k a (s,j) = bump T x V k b (s,j) := by
  rcases j with t|i
  · simp only [bump,Sum.elim_inl, faceKick] at *
    split
    · apply tsum_congr
      intro i; dsimp only; split
      · let P := (T.up.row t.1.2 i).2
        have he := slot_distance (S:=S) P t.1.1
        suffices hl : plaquetteJet S V s (Work.F03.slotFace P t.1.1) a = plaquetteJet S V s (Work.F03.slotFace P t.1.1) b from congr_arg _ (congr_arg (G.adjoint (travel (facade S s V 0) t.1.1 P.walk)) hl)
        apply faceJet_dep
        refine fun e hv => h e ((contains ..).mpr ?_)
        unfold roots; dsimp only [Sum.elim_inl]
        apply (separation_triangle _ (s.act (S.ratio.parent (Work.F03.slotFace P t.1.1).1)) _).trans
        rw [separation_signed]
        unfold span; change _ ≤ _ at he
        have hh : P.length ≤ till x := by assumption
        unfold Slot.length at hh; omega
      · rfl
    · congr 1
      refine faceJet_dep _ s _ a b (fun e he => h e ((contains ..).mpr ?_))
      unfold roots; dsimp only [Sum.elim_inl]; unfold span; omega
  · change -(_ • blockJet V k s i a) = -(_ • blockJet V k s i b)
    rw [blockJet_dep V k s i a b hp ?_]
    refine fun e he => h e ((contains ..).mpr ?_)
    unfold roots; dsimp only [Sum.elim_inr]; unfold span; omega

open Rows
lemma skip_bump (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices)
    (A : Stores S) (F : Forest S.ratio) (s : Signed) (j : Twin f ⊕ Bond c) (a : LogArray G (Active A x F))
    (hp : S.patch.Branches S.kernel G) (hs : ¬ keep x (shots S x) A F (s,j)) :
    bump T x V k (fresh x (shots S x) A F a) (s,j) = 0 := by
  have he : ¬curb (shots S x) A F x s (j.elim (fun x => .inl x.1) Sum.inr) := by
    rcases j with j|j <;> exact hs
  rw [bump_dep T x V k s j _ 0 hp ?_]
  · rcases j with j|j
    · unfold bump; dsimp only; unfold faceKick; simp [barrel]
    · unfold bump; dsimp only; simp [noiseKick]
  intro i hi
  unfold fresh
  split
  · rename_i hn
    split
    · rename_i ht
      exact (he ⟨⟨⟨i,hn⟩,ht⟩,hi⟩).elim
    · rfl
  · rfl

lemma selected_all (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (A : Stores S) (F : Forest S.ratio)
    (a : LogArray G (Active A x F)) (hp : S.patch.Branches S.kernel G) :
    selected T x V k (shots S x) A F (fresh x (shots S x) A F a) = slip • bump T x V k (fresh x (shots S x) A F a) := by
  funext i
  obtain ⟨s,j⟩ := i
  unfold selected Rows.restrict; split
  · rfl
  next hx => rw [Pi.smul_apply,skip_bump _ _ _ _ _ _ _ _ _ hp hx,smul_zero]

/-- All stencils fit. -/
lemma small_span (P : Patch) : ∀ᶠ x in atTop, span P x ≤ radiusB x / 50 := by
  filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop (100*(5+predReach P))] with x hx
  unfold span till; omega

/-- If selection occurs, even the other ends of all its a and potential
frozen-shell inputs are remote (including oriented stencils). -/
lemma guarded {s : Signed} {i : Where S} {A : Stores S} {F : Forest S.ratio}
    (hx : span S.patch x ≤ radiusB x/50) (h : curb (shots S x) A F x s i) :
    let o := s.act (roots S i); let b := radiusB x
    o ∉ A.dome (9*b+9*b/10) ∧
      ∀ e ∈ shots S x s i, S.ratio.parent e.1 ∉ A.dome (9*b+8*b/10) ∧
        S.ratio.parent (e.1+Lattice.step e.2) ∉ A.dome (9*b+8*b/10) := by
  intro o b
  obtain ⟨a,ha⟩ := h
  let l := S.ratio.parent a.val.val.1
  have hv : separation o l ≤ b/50 := ((contains ..).1 ha).trans hx
  have hh (m : Site c) k (h : k + separation m l ≤ 10*b) : m∉A.dome k := by
    intro he
    obtain ⟨y,hy,ht⟩ := halo_spec.mp he
    exact remote a (halo_spec.mpr ⟨y,hy,(separation_triangle y m _).trans ((Nat.add_le_add_right ht _).trans h)⟩)
  have hp : 1 ≤ b := by unfold span at hx; unfold b; omega
  refine ⟨hh _ _ (by omega),fun e he => ?_⟩
  let m := S.ratio.parent e.1
  let n := S.ratio.parent (e.1+Lattice.step e.2)
  have hr : separation m l ≤ b/50+b/50 := by
    apply (separation_triangle _ o _).trans
    rw [separation_comm m o]
    exact Nat.add_le_add (((contains ..).mp he).trans hx) hv
  refine ⟨hh _ _ (by change _+separation m l ≤ _; omega), hh _ _ ?_⟩
  have hk : separation n l ≤ separation n m + separation m l := separation_triangle ..
  rw [separation_comm n m] at hk
  have hu : separation m n ≤ 1 := Work.E03.parent_step ..
  change _ + separation n l ≤ _
  unfold span at hx; unfold b at *
  omega
end YM.Next.SectorChange
