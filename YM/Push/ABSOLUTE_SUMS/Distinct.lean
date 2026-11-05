import YM.Push.ABSOLUTE_SUMS.Breadth
import YM.Push.ABSOLUTE_SUMS.Forest


/-!
# Unnumbered distinct-address forest count

Cancel the one global factorial exactly when estimating families of
distinct occurrences. Includes the sum over their possible labelled
forests. Relation to `Ac.Pack` (every component attaches to the given
support); also useful with root itself a cluster label. Tail includes
all distinct variants WITH THEIR OWN labels whenever supported by the
vertex Hit estimates. No division by orderings of path placements.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Trees
open Lattice Finset RG Relation
open scoped Topology BigOperators Classical
variable {n : Side} {ι : Type*} (X : ι → Support n) (B : ℕ)

section Reindex
variable {Y : Support n} {m : ℕ} {α α' : Type*} (e : α' ≃ α)

def reindex (p : α → Option α) : α' → Option α' := fun i => Equiv.optionCongr e.symm (p (e i))

lemma back_index (p : α → Option α) : reindex e.symm (reindex e p) = p := by
  funext i; simp only [reindex,e.apply_symm_apply,Equiv.symm_symm]
  cases p i <;> simp

lemma growth_reindex {p : α → Option α} (h : Ranked p) : Ranked (reindex e p) := by
  rcases h with ⟨R,h⟩
  refine ⟨R ∘ e,fun i j he => h _ _ ?_⟩
  unfold reindex at he
  cases hk : p (e i) with
  | none => rw [hk] at he; change none = some j at he; contradiction
  | some k =>
    rw [hk] at he; change some (e.symm k) = some j at he
    rw [← Option.some.inj he,e.apply_symm_apply]

lemma reindex_sprouts {p : α → Option α} {z : α → ι} (h : Sprouts X Y p z) :
    Sprouts X Y (reindex e p) (z ∘ e) := by
  refine ⟨growth_reindex e h.1,fun i => ?_⟩
  have he := h.2 (e i)
  unfold reindex
  cases hk : p (e i) with
  | none => rw [hk] at he; exact he
  | some j =>
    rw [hk] at he
    change Ac.meets X (z (e i)) (X (z (e (e.symm j))))
    rw [e.apply_symm_apply]; exact he

lemma forestWeight_reindex [Fintype α] [Fintype α'] (w : ι → ℝ) (a : ℝ) (p : α → Option α)
    (z : α → ι) : forestWeight X B w a Y (reindex e p) (z ∘ e) = forestWeight X B w a Y p z := by
  unfold forestWeight
  by_cases h : Sprouts X Y p z
  · rw [if_pos (reindex_sprouts X e h),if_pos h,Fintype.card_congr e]; congr 1
    exact Fintype.prod_equiv e _ _ fun _ => rfl
  have hc : ¬ Sprouts X Y (reindex e p) (z ∘ e) := fun he => by
    have hk := reindex_sprouts X e.symm he
    simp only [back_index,Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id] at hk
    exact h hk
  simp [hc,h]
end Reindex

/-- Trees on one representative of each chosen address, NONE carrying the
arbitrary external support. -/
abbrev Twig (ι : Type*) := Σ s : Finset ι, (↥s → Option ↥s)
abbrev Choice (ι : Type*) (m : ℕ) := Σ q : Twig ι, (Fin m ≃ q.1)

def number {m : ℕ} (t : Choice ι m) : ForestAt ι m :=
    (reindex t.2 t.1.2,fun i => (t.2 i).val)

lemma number_inj (ι : Type*) (m : ℕ) : Function.Injective (@number ι m) := by
  have he (t : Choice ι m) : t.1.1 = univ.image (number t).2 := by
    ext i; rw [mem_image]; constructor
    · intro hi
      refine ⟨t.2.symm ⟨i,hi⟩,mem_univ _,?_⟩; unfold number; simp
    · rintro ⟨j,-,rfl⟩; exact (t.2 j).property
  rintro ⟨⟨s,p⟩,e⟩ ⟨⟨t,q⟩,f⟩ h
  have ht : s=t := (he ⟨⟨s,p⟩,e⟩).trans
    ((congr_arg (fun z : ForestAt ι m => univ.image z.2) h).trans (he ⟨⟨t,q⟩,f⟩).symm)
  subst t
  change (Fin m ≃ ↥s) at e f
  have he : e=f := Equiv.ext fun i => Subtype.ext (congr_fun (congr_arg Prod.snd h) i)
  subst f
  have hp : p=q := by
    rw [← back_index e p,← back_index e q,
      (show reindex e p=reindex e q from congr_arg Prod.fst h)]
  subst q; rfl

def twigW (Y : Support n) (w : ι → ℝ) (a : ℝ) (t : Twig ι) :=
    if Sprouts X Y t.2 (fun i : ↥t.1 => i.val) then ∏ i ∈ t.1, w i * currency B a (X i) else 0

lemma twig_eq (Y : Support n) (w : ι → ℝ) (a : ℝ) (q : Twig ι) : twigW X B Y w a q =
    q.1.card.factorial * forestWeight X B w a Y q.2 (fun i => i.val) := by
  unfold twigW forestWeight; split
  next he =>
    rw [Fintype.card_coe, Finset.prod_subtype _ (p:=(·∈q.1)) (fun i => Iff.rfl)]
    field_simp
  next he => rw [mul_zero]

lemma number_weight (Y : Support n) (w : ι → ℝ) (a : ℝ) {m : ℕ} (q : Twig ι)
    (ht : q.1.card=m) :
    ∑ e : Fin m ≃ q.1, forestW X B Y w a ⟨m,number (ι:=ι) ⟨q,e⟩⟩ = twigW X B Y w a q := by
  have he (e : Fin m ≃ q.1) : forestW X B Y w a ⟨m, number (ι:=ι) ⟨q,e⟩⟩ =
      forestWeight X B w a Y q.2 (fun i => i.val) := forestWeight_reindex (Y:=Y) X B e w a q.2 (fun i => i.val)
  have e := Fintype.equivOfCardEq (show Fintype.card (Fin m) = Fintype.card q.1 by simp [ht])
  simp only [he, Finset.sum_const,card_univ,Fintype.card_equiv e, Fintype.card_fin,twig_eq,ht,
    nsmul_eq_mul]

lemma twig_pos {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (a : ℝ) (Y : Support n) (t : Twig ι) :
    0 ≤ twigW X B Y w a t := by
  unfold twigW; split
  · exact prod_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
  exact le_rfl

theorem twig_tail {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q)
    (Y : Support n) (m : ℕ) : SumBudget
      (fun t : Twig ι => if m ≤ t.1.card then twigW X B Y w a t else 0)
      (currency B δ Y*q^m*(1-q)⁻¹) := by
  refine budget_degrees_tail (fun t : Twig ι => t.1.card)
    (twig_pos X B h.2.2.2.2.1 a Y) (Real.exp_pos _).le (ready_pos X B h).le
    h.2.2.2.1 ?_ m
  intro k s hk
  let b (u : Choice ι k) := forestW X B Y w a ⟨k,number u⟩
  have he : SumBudget b (currency B δ Y*q^k) := budget_pull number (number_inj _ _)
    (forest_at X B Y h k)
  calc
    _ = ∑ t∈s, ∑ e : Fin k ≃ t.1, b ⟨t,e⟩ := sum_congr rfl fun t ht =>
      (number_weight X B Y w a t (hk t ht)).symm
    _ = ∑ i∈ s.sigma (fun _ => univ), b i := by rw [sum_sigma]
    _ ≤ _ := budget_sum he _

def rootTwigW (w u : ι → ℝ) (a : ℝ) (i : ι × Twig ι) := u i.1 * currency B a (X i.1) *
    twigW X B (X i.1) w a i.2

/-- For use with DISTINCT from root also, just drop those unwanted
terms; here we charge even one extra possible occurrence of the root
among the nonroots. -/
lemma root_twig_tail {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (fun i => u i * currency B (a+δ) (X i)) b)
    (m : ℕ) : SumBudget
      (fun i : ι × Twig ι => if m ≤ i.2.1.card then rootTwigW X B w u a i else 0)
      (b * q^m * (1-q)⁻¹) := by
  let v := q^m*(1-q)⁻¹
  have ho := h.2.2.2.1; have hp := ready_pos X B h
  have hv : 0 ≤ v := by
    have he : 0<1-q := by linarith
    unfold v; positivity
  have he := budget_scale hv he
  rw [mul_assoc b, show b*(q^m*(1-q)⁻¹) = v*b by unfold v; ring]
  refine budget_rows _ _ (fun i => ?_) he
  have hh := twig_tail X B h (X i) m
  have hx := budget_scale (show 0 ≤ u i * currency B a (X i) from
    mul_nonneg (hu _) (Real.exp_pos _).le) hh
  convert hx using 1
  · ext s; split
    next h => rfl
    next h => simp only [mul_zero]
  unfold v; rw [currency_add]; ring

-- Convert to `Pack X Y s`. This estimate does not require summing all choices
-- of parent map (the estimates above include that stronger summation).
lemma rootable (Y : Support n) (s : Finset ι) (h : Ac.Pack X Y s) :
    ∃ p : ↥s → Option ↥s, Sprouts X Y p (fun i => i.val) := by
  let W := installed X Y (fun i : ↥s => i.val)
  let R (i j : Option ↥s) := Ac.meets W j (W i)
  have hh (i : Option ↥s) : ReflTransGen R none i := by
    cases i with
    | none => exact .refl
    | some i =>
      obtain ⟨j,hj,hr,hd⟩ := h i.val i.property
      have hs : ReflTransGen R none (some (⟨j,hj⟩ : s)) := .single hr
      apply ReflTransGen.trans hs
      -- lift the chain, including root if alone
      have he q (hk : Ac.chain X s j q) (hq : q∈s) :
          ReflTransGen R (some (⟨j,hj⟩ : s)) (some ⟨q,hq⟩) := by
        induction hk with
        | refl => exact .refl
        | tail _ ht IH => exact (IH ht.1).tail ht.2.2
      exact he _ hd _
  obtain ⟨p,d,hp⟩ := Breadth.build R (fun _ => 0) hh
  exact ⟨p,Breadth.growth_ranked hp.toGrowth, fun i => hp.edges i⟩





/-- `s` is one nonempty cluster of distinct addresses, tested at i. -/
def sparkW (w u : ι → ℝ) (a : ℝ) (i : ι) (s : Finset ι) :=
    if i∈s ∧ Ac.Spark X s then
      u i * currency B a (X i) * ∏ j ∈ s.erase i, w j * currency B a (X j)
    else 0

lemma spark_tail {w u : ι → ℝ} {a γ δ q b : ℝ} (hu : ∀ i, 0 ≤ u i)
    (h : Ready X B w a γ δ q) (he : SumBudget (fun i => u i * currency B (a+δ) (X i)) b)
    (m : ℕ) : SumBudget
      (fun i : ι × Finset ι => if m ≤ i.2.card-1 then sparkW X B w u a i.1 i.2 else 0)
      (b * q^m * (1-q)⁻¹) := by
  let P := fun i : ι × Finset ι => if m ≤ i.2.card-1 then sparkW X B w u a i.1 i.2 else 0
  have hw := h.2.2.2.2.1
  have hp i : 0 ≤ P i := by
    unfold P sparkW; split
    next he =>
      split
      next he =>
        exact mul_nonneg (mul_nonneg (hu _) (Real.exp_pos _).le) (prod_nonneg fun i _ =>
          mul_nonneg (hw i) (Real.exp_pos _).le)
      next he => exact le_rfl
    next he => exact le_rfl
  let Y : ι × Finset ι → Prop := fun i => i.1∈i.2 ∧ Ac.Spark X i.2 ∧ m ≤ i.2.card-1
  have H i (hi : Y i) := rootable X (X i.1) _ (Ac.excise X hi.2.1 hi.1)
  let f (i : ι × Finset ι) : ι × Twig ι := (i.1,⟨i.2.erase i.1, if he:Y i then
    (H i he).choose else fun _ => none⟩)
  let U := fun i : ι × Twig ι => if m ≤ i.2.1.card then rootTwigW X B w u a i else 0
  have hf i (hi : Y i) : U (f i) = P i := by
    unfold U f; dsimp only
    rw [dif_pos hi, if_pos (by rw [card_erase_of_mem hi.1]; exact hi.2.2),rootTwigW,twigW]
    rw [if_pos (H i hi).choose_spec]; unfold P sparkW
    rw [if_pos hi.2.2,if_pos ⟨hi.1,hi.2.1⟩]
  refine budget_of_sum hp fun t => ?_
  let s := t.filter Y
  have hy i (hi : i∈s) := (mem_filter.mp hi).2
  have he' (i) (hi : i∈s) : ((f i).1,insert (f i).1 (f i).2.1) = i := by
    unfold f; dsimp only; rw [insert_erase (hy i hi).1]
  have hh : Set.InjOn f (s:Set (ι × Finset ι)) := by
    intro i hi j hj he; rw [← he' i hi,← he' j hj,he]
  calc
    _ = ∑ i∈s, P i := (sum_subset (filter_subset ..) fun i hi hj => by
        unfold P sparkW; split
        next he =>
          split
          next ha => exact False.elim (hj (mem_filter.mpr ⟨hi,ha.1,ha.2,he⟩))
          next ha => rfl
        next ha => rfl).symm
    _ = ∑ i∈s.image f, U i := by rw [sum_image hh]; exact sum_congr rfl fun i hi => (hf _ (hy _ hi)).symm
    _ ≤ _ := budget_sum (root_twig_tail X B hu h he m) _

/-- Full product weight with individual cover prices; over clusters with
at least one site hit. Still no assuming convergence of any gas. -/
def touches (w : ι → ℝ) (a : ℝ) (x : Site n) (s : Finset ι) :=
    if Ac.Spark X s ∧ x∈s.biUnion X then ∏ i∈s, w i*currency B a (X i) else 0

lemma touch_tail {w : ι → ℝ} {a γ δ q : ℝ} (h : Ready X B w a γ δ q)
    (x : Site n) (m : ℕ) : SumBudget
      (fun s => if m ≤ s.card-1 then touches X B w a x s else 0)
      (γ*q^m*(1-q)⁻¹) := by
  let g := fun s => if m ≤ s.card-1 then touches X B w a x s else 0
  have hw := h.2.2.2.2.1
  have he s : 0 ≤ g s := by
    unfold g touches; split
    next he => split
               · exact prod_nonneg fun i _ => mul_nonneg (hw i) (Real.exp_pos _).le
               · exact le_rfl
    next he => exact le_rfl
  refine budget_of_sum he fun t => ?_
  let P := fun i : ι × Finset ι => if m ≤ i.2.card-1 then sparkW X B w (hit X w x) a i.1 i.2 else 0
  have hP : SumBudget P (γ*q^m*(1-q)⁻¹) := spark_tail X B (hit_pos X hw x) h (test_hit X B h x) m
  let v s (i : ι) := P (i,s)
  let r := t.biUnion id
  calc
    _ ≤ ∑ s∈t, ∑ i∈r, v s i := sum_le_sum fun s hs => by
      have ht i (_ : i∈r) : 0 ≤ v s i := hP.1 (i,s)
      unfold touches; split
      next he =>
        split
        next hh =>
          obtain ⟨i,hi,hx⟩ := mem_biUnion.mp hh.2
          apply le_trans _ (single_le_sum ht (show i∈r from mem_biUnion.mpr ⟨_,hs,hi⟩))
          unfold v P; rw [if_pos he,sparkW,if_pos ⟨hi,hh.1⟩,hit,if_pos hx]
          exact (Finset.mul_prod_erase _ (fun j => w j * currency B a (X j)) hi).symm.le
        next hh => exact sum_nonneg ht
      next he => exact sum_nonneg ht
    _ = ∑ i∈(r ×ˢ t), P i := by rw [sum_product,sum_comm]
    _ ≤ _ := budget_sum hP _


end YM.Push.AbsoluteSums.Trees
