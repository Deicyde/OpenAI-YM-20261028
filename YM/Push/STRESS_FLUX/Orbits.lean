import YM.Bid.Craft
import YM.Next.BOUNDARY.Unique
import YM.Push.STRESS_FLUX.Jets
import YM.Shift.Breath

/-! Orbit test under the FULL signed cube for coefficients with two antisymmetric pairs.
This is *not* an isotropic-tensor assumption. Shared by Stress.Line's d=4 and d=5 counts. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux
open Function Gauge
open scoped BigOperators Matrix.Norms.Frobenius ContDiff

lemma extend_three (i j k : Axis) (h : i ≠ j) (h' : i ≠ k) (h'' : j ≠ k) :
    ∃ p : Equiv.Perm Axis, p 0=i ∧ p 1=j ∧ p 2=k := by
  have he (a b c : Axis) (hab : a≠b) (hac : a≠c) (hbc : b≠c) : Injective ![a,b,c] := by
    intro x y h; fin_cases x <;> fin_cases y <;> simp_all
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair _ _ (he 0 1 2 (by decide) (by decide) (by decide)) (he i j k h h' h'')
  exact ⟨p,hp 0,hp 1,hp 2⟩
lemma extend_two (i j : Axis) (h : i≠j) : ∃ p : Equiv.Perm Axis, p 0=i ∧ p 1=j := by
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair ![(0:Axis),1] ![i,j]
    (by decide +revert) (by intro a b ha; fin_cases a <;> fin_cases b <;> simp_all)
  exact ⟨p,hp 0,hp 1⟩

private abbrev hits (t i j : Axis) := t=i ∨ t=j
private abbrev parallel (i j k l : Axis) := (i=k ∧ j=l) ∨ (i=l ∧ j=k)

private lemma flip_pair (x i j : Axis) : sign (Signed.mirror x) i * sign (Signed.mirror x) j =
    if (x=i ↔ x=j) then 1 else -1 := by simp only [sign,Signed.mirror,decide_eq_true_eq]; split_ifs <;> simp_all
private lemma flip_of_ne (x i j : Axis) (h : i≠j) : sign (Signed.mirror x) i * sign (Signed.mirror x) j =
    if hits x i j then -1 else 1 := by rw [flip_pair]; unfold hits; split_ifs <;> simp_all

private lemma eq_parallel {p q i j : Axis} (hp : p ≠ q) (h : hits p i j) (h' : hits q i j) : parallel i j p q := by
  obtain h|h := h <;> obtain h'|h' := h' <;> simp_all [parallel]

private lemma forms {p q i j k l : Axis} (hp : i ≠ j)
    (hP : ∀ x, (hits x i j ↔ hits x k l) ↔ (x=p ↔ x=q)) :
    (p=q ∧ parallel k l i j) ∨ ∃ t, p≠q ∧ p≠t ∧ q≠t ∧
      ((parallel i j p t ∧ parallel k l q t) ∨ (parallel k l p t ∧ parallel i j q t)) := by
  by_cases hq : p=q
  · refine Or.inl ⟨hq,eq_parallel hp ((hP i).2 (by rw [hq]) |>.mp (.inl rfl)) ((hP j).2 (by rw [hq]) |>.mp (.inr rfl))⟩
  right
  have he : ¬ (hits p i j ↔ hits p k l) := mt (hP p).1 (by simp [hq])
  have hw : ¬ (hits q i j ↔ hits q k l) := mt (hP q).1 (by simp [Ne.symm hq])
  have ht : hits p i j → hits q i j → False := by
    intro h h'
    have hu := eq_parallel hq h h'
    have hk1 : ¬hits p k l := fun e => he (iff_of_true h e)
    have hk2 : ¬hits q k l := fun e => hw (iff_of_true h' e)
    have hk := (hP k).2 (show (k=p ↔ k=q) by unfold hits at hk1 hk2; grind) |>.2 (Or.inl rfl)
    unfold hits parallel at *; grind
  obtain hi|hi := Classical.em (hits i k l)
  · have hj : ¬hits j k l := by
      intro hv
      have hv := eq_parallel hp hi hv
      unfold parallel hits at *; grind
    have hv := (hP j).not.mp (by simp [hits,hj] at *)
    have hx := (hP i).mp (by simp [hi,hits] at *)
    refine ⟨i,hq,?_,?_,?_⟩ <;> (simp only [hits,parallel] at *; grind)
  have hj : hits j k l := by
    by_contra! hj
    have hv : ¬ (j=p ↔ j=q) := mt (hP j).mpr (by simpa [hits] using hj)
    have hx : ¬ (i=p ↔ i=q) := mt (hP i).mpr (by simpa [hits] using hi)
    unfold hits at *; grind
  have hv := (hP j).mp (show _ from iff_of_true (Or.inr rfl) hj)
  have hx := mt (hP i).mpr (show ¬_ from (by simpa [hits] using hi))
  refine ⟨j,hq,?_,?_,?_⟩ <;> (simp only [hits,parallel] at *; grind)

abbrev Six := Axis → Axis → Axis → Axis → Axis → Axis → ℂ
structure Orbit (A : Six) : Prop where
  law (s : Signed) p q i j k l : A p q i j k l =
    ((sign s p*sign s q)*((sign s i*sign s j)*(sign s k*sign s l))) • A (s.perm p) (s.perm q) (s.perm i) (s.perm j) (s.perm k) (s.perm l)
  swap p q i j k l : A p q i j k l = - A p q j i k l
  reverse p q i j k l : A p q i j k l = - A p q i j l k

private lemma zero_of_neg_self {x : ℂ} (hx : x = - x) : x = 0 := by linear_combination hx/2

private lemma Orbit.stencil {A : Six} (h : Orbit A) (p q i j k l : Axis) (hn : A p q i j k l ≠ 0) :
    i ≠ j ∧ k ≠ l ∧ ((p=q ∧ parallel k l i j) ∨ ∃ t, p≠q ∧ p≠t ∧ q≠t ∧
      ((parallel i j p t ∧ parallel k l q t) ∨ (parallel k l p t ∧ parallel i j q t))) := by
  have hi : i≠j := by rintro rfl; exact hn (zero_of_neg_self (h.swap ..))
  have hk : k≠l := by rintro rfl; exact hn (zero_of_neg_self (h.reverse ..))
  refine ⟨hi,hk, forms hi (fun x => ?_)⟩
  have he := h.law (Signed.mirror x) p q i j k l
  rw [flip_pair x p q,flip_of_ne x i j hi, flip_of_ne x k l hk] at he
  simp only [Signed.mirror,Equiv.refl_apply] at he
  split_ifs at he <;> first | tauto | (exfalso; apply hn; apply zero_of_neg_self; simpa using he)

lemma Orbit.test {A : Six} (h : Orbit A)
    (h1 : A 0 0 0 1 0 1 = 0) (h2 : A 0 0 1 2 1 2 = 0)
    (h3 : A 0 2 0 1 2 1 = 0) (h4 : A 0 2 2 1 0 1 = 0) : ∀ a b i j k l, A a b i j k l = 0 := by
  have perm (s : Equiv.Perm Axis) := h.law ⟨s, fun _ => false⟩
  simp only [sign,Bool.false_eq_true,if_false,one_mul,one_smul] at perm
  have shift (p q i j k l i' j' k' l') (ha : parallel i' j' i j) (hb : parallel k' l' k l) (hz : A p q i j k l=0) : A p q i' j' k' l' = 0 := by
    rcases ha with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> rcases hb with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact hz
    · rw [h.reverse, hz,neg_zero]
    · rw [h.swap,hz,neg_zero]
    rw [h.reverse, h.swap p q _ _ l' k',hz]; simp
  have one (p i j : Axis) (hi : i ≠ j) : A p p i j i j = 0 := by
    have check (i j : Axis) (hi : i ≠ j) : A i i i j i j = 0 := by
      obtain ⟨s,hs,hs'⟩ := extend_two i j hi
      rwa [perm s,hs,hs'] at h1
    by_cases hp : p=i
    · subst i; exact check _ _ hi
    by_cases hq : p=j
    · subst j; exact shift _ _ p i p i _ _ _ _ (Or.inr ⟨rfl,rfl⟩) (Or.inr ⟨rfl,rfl⟩) (check p i hi.symm)
    obtain ⟨s, hs, hS, hJ⟩ := extend_three p i j hp hq hi
    rwa [perm s,hs,hS,hJ] at h2
  have shared (a b t : Axis) (hab : a≠b) (hat : a≠t) (hbt : b≠t) : A a b a t b t=0 ∧ A a b b t a t=0 := by
    obtain ⟨s,hs,hS,hB⟩ := extend_three a t b hat hab hbt.symm
    rw [perm s, hs, hS,hB] at h3 h4
    exact ⟨h3,h4⟩
  intro a b i j k l
  by_contra! he
  obtain ⟨hi,-,⟨rfl,H⟩|⟨t,ht,ha,hb,hk|hk⟩⟩ := h.stencil a b i j k l he
  · exact he (shift _ _ i j i j _ _ _ _ (Or.inl ⟨rfl,rfl⟩) H (one a i j hi))
  · exact he (shift _ _ a t b t _ _ _ _ hk.1 hk.2 (shared a b t ht ha hb).1)
  exact he (shift _ _ b t a t _ _ _ _ hk.2 hk.1 (shared a b t ht ha hb).2)
end YM.StressFlux
