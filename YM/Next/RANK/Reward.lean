import YM.Next.RANK.EntryWord

/-!
# Rooting the gas at restored radii

If right attachments cost a lot ($e^u$), charge all potential meetings with
one to every incident left used in a connected component. This overcharges.
Gives an alternative to the inflated-patch version of the connected-tree
argument in E needed upon enlarging radii. No extra halo volume lost at
this step. Keep full hit tests, including any required support exponent.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.EntryWord
open Lattice Wilson RG Finset MeasureTheory Marker Value Glyph Real
open scoped BigOperators Classical

variable {G : Gauge} {n : Side} {V : Type*} [DecidableEq V] [Fintype V] {ζ : V → Site n} {o : BudgetPoint}
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable (K : ι → Lifted G ζ o.threshold) (F : κ → Refusal G ζ o.threshold)

omit [DecidableEq ι] [DecidableEq κ] in
lemma repriced {r : V → ℝ} (hr : ∀ i,0<r i) (p : Latch K F) (U) :
    Poly.toll r (merged K F p).fires* ‖(merged K F p).value U‖ ≤
      ∏ i ∈ p.val, (Poly.toll r (mode K F i) * ‖score K F i U‖) := by
  rw [← Poly.solo]; change Poly.price r ((merged K F p).amount U) ≤ _; rw [look_inside]; split_ifs
  · apply (Poly.multiple hr _ _).trans; apply le_of_eq; simp only [hook,Poly.solo]
  rw [Poly.zero_price]; exact prod_nonneg fun i _ => mul_nonneg (Poly.worth hr _).le (norm_nonneg _)

variable [Fintype κ]
def promises (F : κ → Refusal G ζ o.threshold) (P : Support n) : Finset κ := univ.filter (fun j => ¬ Disjoint P (F j).extent)

omit [DecidableEq ι] in
private lemma promised (p : Latch K F) : p.val.toRight.card ≤ ∑ i∈p.val.toLeft, (promises F (K i).extent).card := by
  refine le_trans (card_le_card ?_) (card_biUnion_le ..)
  intro i hi; obtain ⟨j,hj,h⟩ := p.property.2.2.2 i hi; exact mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨mem_univ _,h⟩⟩

variable (u v : ℝ)

-- rebates per letter, paid before this step

def landing (j : ι ⊕ κ) : ℝ := Sum.elim (fun i => -(u*(promises F (K i).extent).card+v)) (fun _ => u) j
omit [DecidableEq ι] in
lemma reward (p : Latch K F) (hu : 0≤u) (hv : 0≤v) : ∑ i∈p.val, landing K F u v i ≤ -v := by
  rw [sum_sum_eq_sum_toLeft_add_sum_toRight p.val]
  simp only [landing,Sum.elim_inl,Sum.elim_inr,sum_add_distrib,sum_neg_distrib,sum_const,nsmul_eq_mul, ← mul_sum]
  have hp := mul_le_mul_of_nonneg_left (show (p.val.toRight.card:ℝ) ≤ ∑ i∈p.val.toLeft,((promises F (K i).extent).card:ℝ) by
    exact_mod_cast (promised K F p)) hu
  have he := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ p.val.toLeft.card by exact_mod_cast card_pos.mpr p.property.2.1) hv
  linarith only [hp,he]

variable {r : V → ℝ} {a f g : ℝ} {w : ι ⊕ κ → ℝ}

def owed (p : Latch K F) (w : ι ⊕ κ → ℝ) (v a : ℝ) := Real.exp (-v)* charge o a (keep K F p)* ∏ i ∈ p.val,w i

omit [DecidableEq ι] in
lemma pays (hw : ∀ i, 0 ≤ w i) (h1 : 0≤u) (h2 : 0≤v) (hr : ∀ i,0<r i)
    (he : ∀ i U, Poly.price r (hook K F i U) ≤ Real.exp (landing K F u v i)* w i) (p : Latch K F) :
    Lifted.pays o (merged K F p) r a (owed K F p w v a) := by
  have hc : 0 ≤ charge o a (keep K F p) := (Real.exp_pos _).le
  have hf : 0 ≤ ∏ j ∈ p.val, w j := prod_nonneg fun i _ => hw i
  refine ⟨mul_nonneg (mul_nonneg (Real.exp_pos _).le hc) hf, fun U => ?_⟩
  rw [mul_assoc]; apply (mul_le_mul_of_nonneg_left (repriced K F hr p U) hc).trans
  simp only [hook,Poly.solo] at he
  change charge o a _ * _ ≤ owed _ _ _ _ _ _
  unfold owed; rw [mul_comm (Real.exp (-v)),mul_assoc]
  refine mul_le_mul_of_nonneg_left ((prod_le_prod ?_ (fun i _ => he i U)).trans ?_) hc
  · exact fun i _ => mul_nonneg (Poly.worth hr _).le (norm_nonneg _)
  rw [prod_mul_distrib, ← Real.exp_sum]; exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (reward K F u v p h1 h2)) hf

variable [Fintype ι]
theorem held_over (hw : ∀ i,0 ≤ w i) (hh : Ac.Hit (area K F) o.B w (a+1) g)
    (ha : 0≤a) (hP : (o.B+o.B+1:ℕ)^4*(g:ℝ) ≤ 1) (hG : 0≤g) (x : Site n) :
    ∑ i, (if x∈(merged K F i).extent then owed K F i w v a else 0) ≤ Real.exp (-v)*(Real.exp g-1) := by
  have he := Ac.forest (area K F) o.B ha hw hh hP hG x
  let W := Ac.roots (area K F) o.B w a x
  have hf (p : Latch K F) : (if x∈ (merged K F p).extent then owed K F p w v a else 0) = Real.exp (-v)*W p.val := by
    dsimp only [W,Ac.roots]; simp only [p.property.1,true_and]; split_ifs
    · unfold owed; rw [mul_assoc]; rfl
    · rename_i h1 h2; contradiction
    · rename_i h1 h2; contradiction
    rw [mul_zero]
  simp_rw [hf,← mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have ht := he.2.1.sum_le_tsum ((univ : Finset (Latch K F)).image Subtype.val) (fun i _ => he.1 i)
  rw [sum_image (fun _ _ _ _ h => Subtype.ext h)] at ht
  exact ht.trans he.2.2
end YM.Next.Rank.EntryWord
