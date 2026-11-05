import YM.Next.MULTISOURCE.Collateral

/-! Actual coefficients against the fixed link measures are integrable. -/

set_option autoImplicit false
noncomputable section

namespace YM.Multi
open RG Wilson Lattice Marker Function MeasureTheory Filter
open scoped Topology Matrix.Norms.Frobenius BigOperators
variable {V : Type*} [DecidableEq V] {n : Side} {G : Gauge}

lemma gathers_legible (P : Rep G n) (f : ℕ→Config G n→ℂ)
    (h : ∀ i, Legible P.p (Pack.ofAddress P.activities i) (f i)) (q : Pack n) :
    Legible P.p q (fun U => Pack.collect P (fun i => f i U) q) := by
  unfold Pack.collect
  constructor
  · apply Measurable.tsum; intro i
    split; exact (h i).borel; exact measurable_const
  · intro i x; apply tsum_congr; intro j
    split
    · exact (h j).symmetry i x
    rfl
  · intro U V H H'
    apply tsum_congr; intro i
    split <;> rename_i he
    · have hh := (h i).reads U V (by rw [he]; exact H) (by rw [he]; exact H')
      exact hh
    rfl
  intro U H
  by_contra he
  apply H
  refine (tsum_congr (g:=fun _ : ℕ => (0:ℂ)) ?_).trans tsum_zero; intro i
  split <;> rename_i hu
  · by_contra hk
    apply he; rw [← hu]; exact (h i).inventory U hk
  rfl

lemma collects_bound (P : Rep G n) (k : ℕ → ℝ) (f : ℕ→ℂ) (hs : Summable k) (h : ∀ i,‖f i‖≤k i) (b : Pack n) :
    ‖Pack.collect P f b‖ ≤ Pack.collect P k b := by
  have he := Pack.access P k hs b
  unfold Pack.collect
  let r (i) := if Pack.ofAddress P.activities i=b then f i else 0
  have hf (i) : ‖r i‖ ≤ if Pack.ofAddress P.activities i=b then k i else 0 := by
    unfold r; split; exact h i; exact (norm_zero).le
  have hx := he.of_nonneg_of_le (fun i => norm_nonneg (r i)) hf
  exact (norm_tsum_le_tsum_norm hx).trans (hx.tsum_le_tsum hf he)

lemma incumbent_legible (P : Rep G n) (q : Pack n) (H : P.activities.ForcedFamily P.p) :
    Legible P.p q (fun U => incumbent P U q) := by
  refine gathers_legible P (fun i U => _) (fun i => ?_) q
  exact ⟨Complex.continuous_ofReal.measurable.comp (H.meas i),
    fun t U => congrArg Complex.ofReal (H.sym i t U),
    fun U V hx hv => congrArg Complex.ofReal (H.reads i U V hx hv),
    fun U he => (H.permit i U (fun h => he (h.symm ▸ Complex.ofReal_zero))).1⟩

lemma Credit.integrand {P : BudgetPoint} {q : Support n} {r κ B : ℝ} {D : Pulse G n} (h : Credit P r κ q D B) :
    Envelope D.1 ∧ ∀ i, Envelope (D.2 i) := by
  obtain ⟨hx,h,-,-,⟨i,F,hi,-,-,W,H,f,hf,Hf,hW⟩,g,_,hg⟩ := h
  constructor
  · obtain ⟨C,hC⟩ := (Banked.reserve hx h (fun j => (hf j).2.2.2) Hf).bound
    rw [hi,(show F = _ from funext hW)]
    exact ⟨measurable_const.add (Measurable.tsum fun j => masked_measurable _ _ _ (hf j).2.1.borel), ‖i‖+C,
      fun x => (norm_add_le ..).trans (by simpa only [add_le_add_iff_left] using hC x)⟩
  intro i
  exact ⟨(hg i).1.borel,_,(hg i).2.2.2⟩

namespace Leaf
variable {X : Type*} [MeasurableSpace X] {f g : X→ℂ} {R : Census V} {T B : X → Poly R}
lemma atom (a : ℂ) : Envelope (fun _ : X => a) := ⟨measurable_const, _, fun _ => le_rfl⟩
lemma combine (h : Envelope f) (k : Envelope g) : Envelope fun x => f x+g x := by
  obtain ⟨A,hA⟩ := h.cost; obtain ⟨B,hB⟩ := k.cost
  exact ⟨h.meas.add k.meas,_, fun x => (norm_add_le ..).trans (add_le_add (hA _) (hB _))⟩
lemma multiply (h : Envelope f) (k : Envelope g) : Envelope fun x => f x*g x := by
  obtain ⟨A,hA⟩ := h.cost; obtain ⟨B,hB⟩ := k.cost
  exact ⟨h.meas.mul k.meas, _, fun x => (norm_mul ..).trans_le (mul_le_mul (hA x) (hB x)
    (norm_nonneg _) ((norm_nonneg _).trans (hA x)))⟩
lemma amounts {I : Type*} (s : Finset I) (F : I→X→ℂ) (h : ∀ i, Envelope (F i)) :
    Envelope fun x => ∑ i∈s,F i x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.sum_empty]; exact atom 0
  | insert i s ih hv => simp only [Finset.sum_insert ih]; exact combine (h i) hv

def All (f : X → Poly R) := ∀ T, Envelope fun x => (f x).part T
lemma save (f : Poly R) : All (fun _ : X => f) := fun _ => atom _
lemma insert_ (h : Envelope f) (q : R.Mode) : All fun x => Poly.send q (f x) := by
  intro i; simp only [Poly.part_send]
  split; exact h; exact atom _
lemma add (h : All T) (k : All B) : All fun x => T x+B x := fun i => combine (h i) (k i)
lemma mul (h : All T) (k : All B) : All fun x => T x*B x := by
  intro i; simp only [Poly.part_mul]
  refine amounts _ _ fun j => amounts _ _ fun y => ?_
  split; exact multiply (h j) (k y); exact atom _
lemma smul (h : Envelope f) (k : All T) : All fun x => f x • T x := fun i => multiply h (k i)
lemma sum {I : Type*} (s : Finset I) (F : I → X→Poly R) (h : ∀ i, All (F i)) :
    All fun x => ∑ i∈s,F i x := fun j => by simp_rw [Poly.part_sum]; exact amounts s _ fun i => h i j
lemma prod {I : Type*} (s : Finset I) (F : I → X→Poly R) (h : ∀ i, All (F i)) :
    All fun x => ∏ i∈s,F i x := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.prod_empty]; exact save 1
  | insert i s hi ih => simp only [Finset.prod_insert hi]; exact mul (h i) ih
lemma pow (h : All T) (i : ℕ) : All fun x => T x^i := by
  induction i with
  | zero => simp only [pow_zero]; exact save 1
  | succ i ih => simp only [pow_succ]; exact mul ih h
lemma trigger (p : X → Prop) [DecidablePred p] (H : MeasurableSet {x | p x}) (h : All T) :
    All fun x => if p x then T x else 0 := by
  intro i
  obtain ⟨hs,A,hA⟩ := h i
  simp only [apply_ite Poly.part,ite_apply,Poly.part_nil]
  refine ⟨hs.ite H measurable_const, max A 0, fun x => ?_⟩
  split; exact (hA _).trans (le_max_left ..); exact (norm_zero).le.trans (le_max_right ..)
end Leaf

variable [Fintype V]

lemma throughJet (P : Rep G n) {σ C Λ δ w : ℝ} (H : P.Lawful σ C Λ δ w) {R : Census V}
    (f : Config G n → Poly R) (k : Pack n → Config G n → Poly R) (he : Leaf.All f) (hv : ∀ i, Leaf.All (k i)) :
    Leaf.All fun x => composeAt P x (f x) (fun j => k j x) := by
  classical
  unfold composeAt; refine Leaf.smul ?_ (Leaf.mul ?_ ?_)
  · obtain ⟨he,c,hc⟩ := (P.exponentEnv H).exp
    exact ⟨Complex.continuous_ofReal.measurable.comp he,c, fun x => by
      rw [Complex.norm_real]; exact hc x⟩
  · refine Leaf.sum _ _ (fun i => Leaf.smul (Leaf.atom _) (Leaf.pow he i))
  obtain ⟨p,hp,hP⟩ := Activities.K_total H.labels.boundK
  simp_rw [Pack.clears, Finset.sum_filter]
  refine Leaf.sum _ _ fun i => ?_
  apply Leaf.trigger
  · simpa only [Pack.clears,Finset.mem_filter,Finset.mem_univ,true_and]
      using Pack.neighborhood (G:=G) i P.p.threshold
  refine Leaf.prod _ _ fun j => Leaf.add (Leaf.insert_ ?_ _) (hv _)
  refine ⟨(incumbent_legible P j H.labels.forced).borel, _, fun x => collects_bound P p (fun i => (P.activities.K i x:ℂ)) hp (fun i => ?_) j⟩
  rw [Complex.norm_real]; exact (hP i).2 x

lemma evaluate_int (P : Rep G n) {σ C Λ δ w : ℝ} (H : P.Lawful σ C Λ δ w) {R : Census V} (D : V → Pulse G n)
    {r κ : ℝ} {X : V → Support n} {h : V → ℝ} (he : ∀ i, Credit P.p r κ (X i) (D i) (h i)) (T : R.Mode) :
    Integrable (jet P R D T) (prior G n) := by
  have hg : Leaf.All (polar P R D) := throughJet P H _ _
    (Leaf.sum _ _ fun i => Leaf.insert_ ((he i).integrand.1) _) fun i =>
      Leaf.sum _ _ fun j => Leaf.insert_ ((he j).integrand.2 _) _
  obtain ⟨hu,C,hC⟩ := hg T
  exact Integrable.of_bound hu.aestronglyMeasurable C (Eventually.of_forall hC)
end YM.Multi
