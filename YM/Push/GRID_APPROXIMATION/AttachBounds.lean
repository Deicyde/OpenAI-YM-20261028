import YM.Next.FOUNDATIONS.SU2
import YM.PREC.Derivative
import YM.Push.GRID_APPROXIMATION.AttachActive
import YM.Work.B04
import YM.Work.B06

/-!
# Quantitative attachment price, any k in the history

Input hypotheses for upstream *birth*, not assumed of a Family.Makes or
Frame. One workable positive-margin budget: multiply the cost of *every*
old forced carrier by `1/ρ`, not relying on the first hit being a fresh root,
and buy one exponential reserve *in the B-scale*. End calculation must still
pay enough W at the later fixed stop. Here proving estimates for the attached
Bands at birth including old and mixed forced characteristics. See Bridges
for use in obligations upstream of Grill. No claiming one-step RG or planner
or hereditary merges implemented. This gives special birth estimates with
explicit gain factor, summability, BEFORE that propagation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Push.GridApprox.Attach
open RG Lattice Wilson Cells MeasureTheory Measure Function Filter Finset Ac Marker Overlay Nil
open scoped Topology BigOperators
variable {G : Gauge} {n : Side} {V : Type*} [Fintype V] [DecidableEq V] {R : Census V}
    {P : Rep G n} {a : Bands R P}

/-- Paying new births relative to Marker weights w. Root prices independent
of number of copies. Does **not** assert convergence of hierarchical summations.
`ρ` the extra forced denominator price, needs hits of old letters already
small also after that price. -/
structure Launch (I : Plan a) (w : V → ℝ) (u c ρ γ : ℝ) : Prop where
  positive : 0 < ρ
  inflate : ρ ≤ 1
  fit : (((P.p.B+P.p.B+1:ℕ):ℝ)^4)*γ ≤ 1
  nonneg : 0≤γ
  global i : w i * ‖I.c i‖ ≤ u
  sectionBound i : ∃ r : ℝ, P.p.supBounds (a.origins i) (I.Y i) (I.F i) r ∧
      w i * P.p.mass (I.Y i) r ≤ c
  -- majorant of the old `each` array and New `peel` arrays, uniform at
  -- every configuration. One spare exponential for tree recursion. Ignore
  -- other reservations unless bought in this query.
  crew : ∃ f : Alphabet V → ℝ, (∀ i, 0≤ f i) ∧ Hit (patch I) P.p.B f (P.p.supportExponent+1) γ ∧
      ∀ i, ∃ U : Nil.Sheet R, 0 ≤ U ∧ wordsPrice w U ≤ i.elim (fun _ => ρ) (fun _ => 1) * f i ∧
        ∀ x j, ‖(leaf I i x).part j‖ ≤ U j

section prices
variable {I : Plan a} (T : Spares I) [Nonempty V]
variable {w : V → ℝ} {ρ γ δ κ u c d b u' c' : ℝ}
  (hr : P.activities.Valid P.p δ κ) (ha : a.Active) (ht : a.Radial w u c d b)
  (hd : Launch I w u' c' ρ γ)

include ht hd in
private lemma packet_prices (f : Alphabet V → ℝ) (hf : ∀ i,0≤f i)
    (hm : ∀ i, ∃ U : Nil.Sheet R, 0 ≤ U ∧ wordsPrice w U ≤ i.elim (fun _ => ρ) (fun _ => 1)*f i ∧
        ∀ x j, ‖(leaf I i x).part j‖ ≤ U j) (j : Block I) :
    ∃ U : Nil.Sheet R, 0 ≤ U ∧ wordsPrice w U ≤ ρ * ∏ i∈j.val, f i ∧ ∀ x s, ‖(connection T j x).part s‖ ≤ U s := by
  let p (i : Alphabet V) := i.elim (fun _ => ρ) (fun _ => 1)
  choose q hq hv he using hm
  obtain ⟨M,hN,hL,hV⟩ := all_prices j.val q (fun i => p i * f i) (fun x i => leaf I i x)
    w ht.pure hq hv (fun x i => he i x)
  have hρ := hd.positive
  refine ⟨M,hN,hL.trans ?_,fun x s => ?_⟩
  · obtain ⟨i,hi⟩ := j.property.1.1
    rw [prod_mul_distrib]
    have hp0 (i : Alphabet V) : 0 ≤ p i := by cases i; exacts [hρ.le,zero_le_one]
    have hp (i : Alphabet V) : p i ≤ 1 := by cases i; exacts [hd.inflate,le_rfl]
    apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun i _ => hf i)
    calc
      _ ≤ ∏ l∈ ({Sum.inl i} : Finset (Alphabet V)), p l := prod_le_prod_of_subset_of_le_one
        (Finset.singleton_subset_iff.mpr (mem_toLeft.mp hi)) (fun v _ => hp0 v) (fun v _ _ => hp v)
      _ = ρ := by rw [prod_singleton]; rfl
  unfold connection; split
  · exact hV x s
  rw [Poly.part_nil,norm_zero]; exact hN s

include hr ha ht hd in
private lemma hits_bound :
    ∃ t : ℕ × ℕ → ℝ, (∀ i j, 0≤ t (i,j) ∧ ∀ U, ‖(attached T).entries i j U‖ ≤ t (i,j)) ∧
    ∀ i : V, SumBudget (fun k => if i∈ ((attached T).marks k.1 k.2).val then
      Poly.toll w ((attached T).marks k.1 k.2)*P.p.mass (P.activities.forced k.1).support (t k) else 0)
      (d*b + ρ*(Real.exp γ-1)) := by
  classical
  obtain ⟨f,hf,hH,hm⟩ := hd.crew
  let Z := attached T
  have he (j : Block I) := packet_prices T (ht:=ht) (hd:=hd) f hf hm j
  choose M hN hL hV using he
  obtain ⟨τ,hτ,hR⟩ := ht.hits
  let t : ℕ × ℕ → ℝ := fun k => if hh : ∃ p, T.tag p=k.1 then
      (if Z.entries k.1 k.2 = 0 then 0 else M hh.choose (Z.marks k.1 k.2)) else τ k
  have ot (q i) (h : ∀ p, T.tag p ≠ q) : t (q,i) = τ (q,i) := by unfold t; simp only [show ¬ ∃ p,T.tag p = q by tauto,↓reduceDIte]
  have nt (j : Block I) i : t (T.tag j,i) = if Z.entries (T.tag j) i=0 then 0 else M j (Z.marks (T.tag j) i) := by
    unfold t; dsimp only; split_ifs with hh hi
    · rfl
    · rw [T.injective hh.choose_spec]
    all_goals exact False.elim (hh ⟨_,rfl⟩)
  have hy i j : 0 ≤ t (i,j) ∧ ∀ U, ‖Z.entries i j U‖ ≤ t (i,j) := by
    by_cases h : ∃ p,T.tag p=i
    · obtain ⟨p,rfl⟩ := h; rw [nt]; split
      next he => rw [he]; simp
      next he =>
        refine ⟨hN p _, fun U => ?_⟩
        by_cases hh : ∃ s : R.Mode, s.val.Nonempty ∧ code s=j
        · obtain ⟨s,hs,rfl⟩ := hh; unfold Z; rw [entry_in T _ _ hs, mark_in T _ _ hs]
          exact hV p U s
        exact False.elim (he (entry_extra T p j (by push Not at hh; exact hh)).1)
    push Not at h; rw [ot i j h]; unfold Z; rw [entry_out T i h j]; exact hτ i j
  refine ⟨t,hy,fun i => ?_⟩
  let W (n : ℕ) (q : R.Mode) c := if i∈q.val then Poly.toll w q * P.p.mass (P.activities.forced n).support c else 0
  let C (k : ℕ × ℕ) := W k.1 (Z.marks k.1 k.2) (t k)
  let D (k : ℕ × ℕ) := W k.1 (a.marks k.1 k.2) (τ k)
  have hb : SumBudget D (d*b) := hR i
  have hz (k : ℕ × ℕ) : 0 ≤ C k := by
    unfold C W; split
    · apply mul_nonneg (Poly.worth ht.pure _).le; unfold BudgetPoint.mass; exact mul_nonneg (Real.exp_pos _).le (hy k.1 k.2).1
    exact le_rfl
  let X := Ac.roots (patch I) P.p.B f P.p.supportExponent (a.origins i)
  have hh : SumBudget X (Real.exp γ-1) := Ac.forest _ _ P.p.exponent_pos.le hf hH hd.fit hd.nonneg _
  have hρ := hd.positive.le
  have hT (q : ℕ) (s : Finset ℕ) : ∑ k∈s,C (q,k) ≤ (∑ k∈s,D (q,k))+ρ*X (group T q) := by
    by_cases hu : ∃ p,T.tag p=q
    · obtain ⟨l,rfl⟩ := hu
      apply le_trans _ (le_add_of_nonneg_left (sum_nonneg (fun k _ => hb.1 _)))
      rw [group_inside]
      by_cases ht' : a.origins i∈sheet I l.val
      · have hp := l.property.1.2.1
        unfold X Ac.roots
        change _ ≤ ρ* (if Ac.Spark _ _ ∧ a.origins i ∈ sheet I l.val then
          Real.exp (P.p.supportExponent*coverNumber P.p.B (sheet I l.val)) * ∏ i∈l.val,f i else 0)
        rw [if_pos ⟨hp,ht'⟩,mul_left_comm]
        let a' := Real.exp (P.p.supportExponent*coverNumber P.p.B (sheet I l.val))
        apply le_trans _ (mul_le_mul_of_nonneg_left (hL l) (Real.exp_pos _).le)
        change _ ≤ a' * wordsPrice w (M l)
        let m := Finset.univ.filter (fun s : R.Mode => s.val.Nonempty)
        have hv (k : ℕ) (h : k ∉ m.image code) : C (T.tag l,k)=0 := by
          unfold C W; simp only; rw [nt l k]
          rw [if_pos (show _ = _ from (entry_extra T l k (fun s hs he => h (mem_image.mpr ⟨s,mem_filter.mpr ⟨mem_univ _,hs⟩,he⟩))).1)]
          unfold BudgetPoint.mass; split <;> simp
        calc
          _ = ∑ k ∈ s∩m.image code,C (T.tag l,k) := by
            symm; apply sum_subset (inter_subset_left); intro k hk hh; exact hv k (fun h => hh (mem_inter.mpr ⟨hk,h⟩))
          _ ≤ ∑ k∈m.image code,C (T.tag l,k) := sum_le_sum_of_subset_of_nonneg inter_subset_right fun k _ _ => hz _
          _ = ∑ j∈m,C (T.tag l,code j) := sum_image code_inj.injOn
          _ ≤ ∑ j∈m,a'* (Poly.toll w j*M l j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hJ := (mem_filter.mp hj).2
            have hx : Z.marks (T.tag l) (code j)=j := mark_in T l j hJ
            have ht := Poly.worth ht.pure j
            unfold C W; simp only; rw [nt l (code j),hx]
            have hn : 0 ≤ M l j := hN l j
            unfold BudgetPoint.mass a'
            rw [T.full]; split_ifs
            · rw [mul_zero,mul_zero]; positivity
            · exact le_of_eq (mul_left_comm _ _ _)
            positivity
          _ ≤ _ := by
            unfold wordsPrice a'
            rw [Finset.mul_sum]; apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            intro i _ _; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Poly.worth ht.pure _).le (hN _ _))
      have hp k : C (T.tag l,k)=0 := by
        unfold C W; dsimp only; split
        next h =>
          have he : Z.entries (T.tag l) k=0 := by
            by_contra hn
            have hT := (operates hr ha ht T).retained _ _ hn i h
            rw [T.full] at hT; exact ht' hT
          rw [nt l k,if_pos he]; simp only [BudgetPoint.mass,mul_zero]
        rfl
      simp_rw [hp,Finset.sum_const_zero]; exact mul_nonneg hρ (hh.1 _)
    push Not at hu
    have ht k : C (q,k)=D (q,k) := by
      unfold C D Z
      rw [ot q k hu]; rw [mark_out T q hu k]
    simp_rw [ht]; exact le_add_of_nonneg_right (mul_nonneg hρ (hh.1 _))
  have hx (s : Finset (ℕ × ℕ)) : ∑ x∈s,C x ≤ d*b + ρ*(Real.exp γ-1) := by
    let x := s.image Prod.fst; let y := s.image Prod.snd
    calc
      _ ≤ ∑ k∈x ×ˢ y, C k := Finset.sum_le_sum_of_subset_of_nonneg (fun k hk =>
        mem_product.mpr ⟨mem_image_of_mem _ hk,mem_image_of_mem _ hk⟩) (fun k _ _ => hz _)
      _ = ∑ i∈x, ∑ k∈y, C (i,k) := sum_product ..
      _ ≤ ∑ i∈x, ((∑ k∈y, D (i,k))+ρ*X (group T i)) := sum_le_sum fun i _ => hT i y
      _ ≤ _ := by
        rw [sum_add_distrib,← mul_sum,← sum_product' x y (fun i j => D (i,j))]
        apply add_le_add ((hb.2.1.sum_le_tsum _ (fun i _ => hb.1 _)).trans hb.2.2)
        rw [← Finset.sum_image (s:=x) (f:=X) (group_injective T).injOn]
        exact mul_le_mul_of_nonneg_left ((hh.2.1.sum_le_tsum _ (fun i _ => hh.1 _)).trans hh.2.2) hρ
  have hv := summable_of_sum_le hz hx
  exact ⟨hz,hv,hv.tsum_le_of_sum_le hx⟩

-- Bulk & hits use unbounded families, no Fubini guessed.
include hr ha ht hd in
theorem sails : (attached T).Active ∧ (attached T).Radial w (u+u') (c+c') (d+(ρ*(Real.exp γ-1))/b) b := by
  have he (i : V) : w i*‖(attached T).units i‖ ≤ u+u' := (
    mul_le_mul_of_nonneg_left (norm_add_le ..) (ht.pure i).le).trans (by rw [mul_add]; exact add_le_add (ht.localU _) (hd.global _))
  refine ⟨operates hr ha ht T,ht.pure,he,ht.factor,?_,?_⟩
  · obtain ⟨t,hB,hQ⟩ := ht.bulk
    choose p hp hm using hd.sectionBound
    let Z : ℕ → ℝ := fun i => (shapes V i).elim t p
    refine ⟨Z,fun i => ?_,fun i => ?_⟩
    · dsimp only [attached,Z]; cases shapes V i with
      | inl i => exact hB _
      | inr j => exact ⟨(hp j).1,fun i hi => Finset.mem_singleton.mp hi |>.symm ▸ hp _⟩
    let X : ℕ → ℝ := fun j => if i ∈ (a.rays j).val then Poly.toll w (a.rays j) * P.p.mass (a.support j) (t j) else 0
    classical
    let Y : V → ℝ := fun x => if i=x then w i*P.p.mass (I.Y x) (p x) else 0
    let W := Sum.elim X Y
    have hb j : _ = W (shapes V j) := show
        (if i∈ ((attached T).rays j).val then Poly.toll w ((attached T).rays j)*P.p.mass ((attached T).support j) (Z j) else 0) = _ from by
      have he (x : Alphabet V) :
          (if i∈ ((x.elim a.rays R.fire)).val then Poly.toll w (x.elim a.rays R.fire) * P.p.mass (x.elim a.support I.Y) (x.elim t p) else 0) = W x := by
        cases x with
        | inl j => rfl
        | inr j => by_cases he : i=j <;> simp [W,Y,Census.fire,Poly.toll,he]
      exact he _
    have hR : SumBudget X c := hQ i
    have hY : Summable Y := Summable.of_finite
    have he : Summable W := Summable.sum _ (show Summable X from hR.2.1) hY
    simp_rw [hb]; refine ⟨fun j => ?_, (shapes V).summable_iff.mpr he,?_⟩
    · have he (x : Alphabet V) : 0 ≤ W x := by
        cases x with
        | inl j => exact hR.1 j
        | inr j =>
          change 0 ≤ Y j; unfold Y; split
          next hx => exact mul_nonneg (ht.pure _).le ((hp j).1.trans (P.p.loMass _ _ (hp j).1))
          next hx => exact le_rfl
      exact he _
    rw [Equiv.tsum_eq,Summable.tsum_sum (f:=W) (show Summable X from hR.2.1) hY ,tsum_fintype (fun x : V => W (Sum.inr x))]; change (∑' i,X i) + (∑ i,Y i) ≤ _; apply add_le_add hR.2.2
    simpa [W,Y] using hm i
  obtain ⟨t,hf,hw⟩ := hits_bound T hr ha ht hd
  refine ⟨t,hf,fun i => ?_⟩
  rw [add_mul,div_mul_cancel₀ _ ht.factor.ne']; exact hw _
end prices
end YM.Push.GridApprox.Attach
