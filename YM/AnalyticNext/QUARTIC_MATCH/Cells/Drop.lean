import YM.AnalyticNext.QUARTIC_MATCH.Cells.LiftOne

/-!
# Drop a leg at its obstruction, preserving all other legs

In momentum the total is evaluation at that momentum zero. No periodic
orbits assumed. When restoring, don't preserve closure in the chosen root.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Filter Topology Laurent
open scoped Topology BigOperators

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {n : ℕ} {σ C : ℝ}

def cut (F : ArrayC (Fin (n+1)) ℤ V) (X : Fin n → Cell ℤ) :=
    ∑' u : Cover, F (Fin.cons (u,∅) X)

def blank (j : Fin n) (F : ArrayC (Fin n) ℤ V) (X : Fin (n+1) → Cell ℤ) :=
    if X 0=((X j.succ).1,∅) then F (Fin.tail X) else 0

namespace Drop


lemma update_cons (X : Fin n →Cell ℤ) (j : Fin n) (b x : Cell ℤ) :
    update (Fin.cons b X : Fin (n+1)→Cell ℤ) j.succ x = (Fin.cons b (update X j x) : Fin (n+1)→Cell ℤ) := by
  funext k; refine Fin.cases ?_ (fun r => ?_) k
  · simp [Ne.symm (Fin.succ_ne_zero _)]
  by_cases h : r=j <;> simp [h]
lemma update_head (X : Fin (n+1)→Cell ℤ) (x : Cell ℤ) :
    update X 0 x = Fin.cons x (Fin.tail X) := by
  funext k; refine Fin.cases ?_ (fun r => ?_) k
  · simp
  simp [Fin.tail]

variable {A : ArrayC (Fin (n+1)) ℤ V} {B : ArrayC (Fin n) ℤ V}

omit [NormedSpace ℝ V] in
lemma EmptySum_iff : EmptySum A 0 ↔ cut A=0 := by
  constructor
  · intro h; funext X
    simpa only [cut,peek,update_head,Fin.tail_cons, Pi.zero_apply] using h (Fin.cons (0,∅) X)
  intro h X; simp_rw [peek, update_head]; exact congr_fun h (Fin.tail X)

omit [NormedSpace ℝ V] in
lemma priced_blank (j : Fin n) (h : Pricing B σ C) : Pricing (blank j B) σ C := by
  refine ⟨?_,h.rate,h.cap,?_⟩
  · intro b X; simp only [blank,move,Function.comp_apply,Prod.mk.injEq]
    have he : (X 0).1=(X j.succ).1 ∧ (X 0).2=∅ ↔ X 0=((X j.succ).1,∅) := by rw [Prod.ext_iff]
    simp only [add_left_inj, he]; split
    · exact h.same b _
    rfl
  intro X i k
  unfold blank; split
  · rename_i H
    have he i : ∃ a, (X i).1=((Fin.tail X) a).1 := by
      refine Fin.cases ⟨j,show (X 0).1=(X j.succ).1 by rw [H]⟩ (fun q => ⟨q,rfl⟩) i
    obtain ⟨a,ha⟩ := he i; obtain ⟨b,hb⟩ := he k
    rw [ha,hb]; exact h.each _ _ _
  rw [norm_zero]; exact mul_nonneg h.cap (cost_size ..)

omit [NormedSpace ℝ V] in
lemma rank_cut (j : Fin n) {k} (h : Rank A j.succ k) : Rank (cut A) j k := by
  intro X hx; unfold cut
  have he (u : Cover) : A (Fin.cons (u,∅) X)=0 := h _ (by simp [hx])
  simp [he]
omit [NormedSpace ℝ V] in
lemma rank_blank (j : Fin n) {l k} (h : Rank B l k) : Rank (blank j B) l.succ k := by
  intro X H; unfold blank; split
  · exact h _ H
  rfl
omit [NormedSpace ℝ V] in
lemma rank_at (j : Fin n) : Rank (blank j B) 0 0 := by
  intro X H; unfold blank; split
  · rename_i he; exfalso; apply H; rw [he]; rfl
  rfl
omit [NormedSpace ℝ V] in
lemma cut_blank (j : Fin n) : cut (blank j B) = B := by funext X; simp [cut,blank]

lemma closed_blank (j l : Fin n) (hj : j≠l) (h : ClosedSlot B l) : ClosedSlot (blank j B) l.succ := by
  funext X
  change rim (peek l.succ X (blank j B)) (X l.succ) = _
  by_cases he : X 0 = ((X j.succ).1,∅)
  · rw [show peek l.succ X (blank j B) = peek l (Fin.tail X) B by
      funext y; simp [peek,blank,hj,he,Ne.symm (Fin.succ_ne_zero _)]]
    rw [h.peek]; rfl
  rw [show peek l.succ X (blank j B) = 0 by funext y; simp [peek,blank,hj,he,Ne.symm (Fin.succ_ne_zero _)], map_zero]; rfl

omit [NormedSpace ℝ V] in
lemma scaled (h : Pricing A σ C) (j : Fin n) (X : Fin n→Cell ℤ) :
    Summable fun u : Cover => ‖A (Fin.cons (u,∅) X)‖ := by
  have he := h.sum_leg (l:=0) (Fin.succ_ne_zero j) (Fin.cons (0,∅) X) ∅
  simpa only [peek,update_head,Fin.tail_cons] using he

def loss (σ : ℝ) := bill (σ/2)
lemma loss_pos (h : 0<σ) : 0 < loss σ := billed (by linarith)

omit [NormedSpace ℝ V] in
lemma cut_both (h : Pricing A σ C) : Pricing (cut A) (σ/2) (loss σ*C) := by
  have hk := h.rate
  refine ⟨?_,by positivity,mul_nonneg (loss_pos hk).le h.cap,?_⟩
  · intro b X
    have hh (u : Cover) : A (Fin.cons (u,∅) (move b ∘ X))=A (Fin.cons (u-b,∅) X) := by
      rw [← h.same b (Fin.cons (u-b,∅) X), show move b ∘ Fin.cons (u-b,∅) X=Fin.cons (u,∅) (move b ∘ X) by
        funext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp [move]]
    unfold cut; simp_rw [hh]; exact Equiv.tsum_eq (Equiv.subRight b) fun u => A (Fin.cons (u,∅) X)
  intro X i j
  let L := cost (σ/2) (X i).1 (X j).1
  have hg x : ‖A (Fin.cons (x,∅) X)‖ ≤ C*L*cost (σ/2) x (X j).1 := by
    have hu := h.each (Fin.cons (x,∅) X) i.succ j.succ
    have hv := h.each (Fin.cons (x,∅) X) 0 j.succ
    simp only [Fin.cons_succ, Fin.cons_zero, cost] at hu hv
    unfold L cost; rw [mul_assoc,← Real.exp_add]
    by_cases H : size (x-(X j).1) ≤ size ((X i).1-(X j).1)
    · apply hu.trans; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap
      nlinarith [Nat.cast_le (α:=ℝ).mpr H]
    apply hv.trans; apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap
    nlinarith [Nat.cast_le (α:=ℝ).mpr (le_of_not_ge (show ¬ size ((X i).1-(X j).1)≥_ from H))]
  let M x := cost (σ/2) x (X j).1
  have hp := accounted (X j).1 (show 0<σ/2 by positivity)
  unfold cut; change _ ≤ loss σ*C*L
  have hs := scaled h j X
  refine ((norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hg (hp.2.1.mul_left (C*L)))).trans ?_
  rw [tsum_mul_left, show loss σ*C*L=C*L*loss σ by ring]
  exact mul_le_mul_of_nonneg_left hp.2.2 (mul_nonneg h.cap (cost_size ..))

variable [CompleteSpace V]


lemma cut_lower (j : Fin n) (h : Pricing A σ C) : cut (lower j.succ A)=lower j (cut A) := by
  funext X
  have hw (u : Cover) (x : Cell ℤ) : peek j.succ (Fin.cons (u,∅) X) A x=A (Fin.cons (u,∅) (update X j x)) := by
    rw [peek,update_cons]
  have hs (x) : Summable fun u : Cover => peek j.succ (Fin.cons (u,∅) X) A x := by
    simp_rw [hw]; exact (scaled h j _).of_norm
  have hz (i) : Summable fun u : Cover => sect i (peek j.succ (Fin.cons (u,∅) X) A) (X j) := by
    simp_rw [sect_at]; split
    · simp
    exact ((hs _).sub (hs _)).const_smul _
  unfold cut; simp_rw [lower_at, Fin.cons_succ]
  rw [Summable.tsum_finsetSum]; swap; exact fun i _ => hz i
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [sect_at,hw]; split
  · simp
  rw [tsum_const_smul'', ( (scaled h j _).of_norm).tsum_sub ((scaled h j _).of_norm)]; rfl

lemma closed_cut (j : Fin n) (h : Pricing A σ C) (hq : ClosedSlot A j.succ) : ClosedSlot (cut A) j := by
  rw [ClosedSlot,← cut_lower j h,hq]; unfold cut; funext x; simp
lemma emptied (j : Fin n) (h : Pricing A σ C) : cut (lower 0 A)=0 := by
  apply EmptySum_iff.mp; intro X
  have hs : sums (peek 0 X A) := fun S => (h.sum_leg (Fin.succ_ne_zero j) _ S).of_norm
  simp_rw [peek_lower]; exact totals hs
omit [NormedSpace ℝ V] in
lemma cut_sub (j : Fin n) (h : Pricing A σ C) {D η v} (g : Pricing D η v) : cut (A-D)=cut A-cut D := by
  funext X; exact (scaled h j X).of_norm.tsum_sub (scaled g j X).of_norm
end Drop
end YM.AnalyticNext.QuarticMatch.BoxChain
