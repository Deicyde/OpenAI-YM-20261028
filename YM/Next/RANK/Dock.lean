import YM.Next.RANK.DockBudget
import YM.Next.RANK.LocalShift

/-!
# Output from the middle estimates

Conditional on the aligned W budgets, geometry and force estimates.
Produces Value.Notice on the corrected polynomial with restored radii and
retains K hit suppression over the expanded footprints. No fake separation of
possibly overlapping refusals. Only cumulative output; need another real step
estimate to finish restoration.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Dock
open Lattice Wilson RG Marker Glyph Camp EntryWord Value Finset Filter
open scoped Topology BigOperators Classical

variable {G : Gauge} {n : Side} {o : BudgetPoint}
variable {A V : Type} [DecidableEq A] [DecidableEq V] [Fintype A] [Fintype V]
variable {Q : A → Support n} {ζ : A × V → Site n}
variable {ι κ : Type} [Fintype ι] [Fintype κ] {m : ℕ}
variable (J : Change o m) (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B)
variable {K : κ → Lifted G ζ o.threshold} {F : A × flame V → Refusal G ζ o.threshold} (hf : ∀ i,(F i).extent=Q i.1)

include hf in
omit [Fintype κ] in
private theorem fee_work (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B) (i : κ) : J.narrow*(K i).fires.val.card+J.fee*(promises F (K i).extent).card ≤
    J.spare*coverNumber o.B (K i).extent + m*J.narrow+ ((2^m:ℕ):ℝ)*J.fee := by
  let I := (touchedBy Q (K i).extent).card
  have hp : (K i).fires.val.card ≤ I*m := (Camp.counted _).trans (Nat.mul_le_mul (card_le_card
    (included Q ζ h.1 _ (K i).fires (K i).remembers)) hm)
  have ht : Fintype.card (flame V)≤2^m := fire_size.trans (pow_le_pow_right₀ (by norm_num) hm)
  have hh : (promises F (K i).extent).card ≤ I*(2^m) := by rw [sworn hf]; exact Nat.mul_le_mul_left _ ht
  have h1 := mul_le_mul_of_nonneg_left (show ((K i).fires.val.card:ℝ) ≤ (I:ℝ)*m by exact_mod_cast hp) J.narrow_cost
  have h2 := mul_le_mul_of_nonneg_left (show ((promises F (K i).extent).card:ℝ) ≤ (I:ℝ)*((2^m:ℕ):ℝ) by exact_mod_cast hh) J.fee_cost
  have hz : 0 ≤ (m:ℝ)*J.narrow := mul_nonneg (Nat.cast_nonneg _) J.narrow_cost; have hy : 0 ≤ ((2^m:ℕ):ℝ)*J.fee := mul_nonneg (Nat.cast_nonneg _) J.fee_cost
  by_cases hz' : 2≤I
  · have he : (m*J.narrow+J.fee*((2^m:ℕ):ℝ))*I ≤ J.spare*coverNumber o.B (K i).extent := dispersal_cost h _ J.spare_cost J.force_pack hz'
    linarith only [h1,h2,hz,hy,he]
  have hh : (I:ℝ) ≤ 1 := by exact_mod_cast (by omega : I≤1)
  have h6 : 0 ≤ J.spare* ↑(coverNumber o.B (K i).extent) := mul_nonneg J.spare_cost (Nat.cast_nonneg _)
  linarith only [h6,h1,h2,mul_le_mul_of_nonneg_left hh hz,mul_le_mul_of_nonneg_left hh hy]

private def eK (J : Change o m) := Real.exp (m*J.narrow + J.fee * ((2^m:ℕ):ℝ)+J.reserve)
private def budgetK (K : κ → Lifted G ζ o.threshold) (C : κ → ℝ) (i : κ) := eK J*C i / charge o (J.e+1) (K i).extent

include hf in
omit [Fintype κ] in
private lemma left_work (C : κ → ℝ) (i : κ)
    (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B)
    (hc : Lifted.pays o (K i) (fun _ => J.m0) (J.e+1+J.spare) (C i)) (U : Config G n) :
    Poly.price (fun _ => J.radius) (hook K F (.inl i) U) ≤
      Real.exp (landing K F J.fee J.reserve (.inl i))* budgetK J K C i := by
  let x := K i
  let P := x.extent
  let D := coverNumber o.B P
  let E : ℝ := m*J.narrow + J.fee * ((2^m:ℕ):ℝ)+J.reserve
  let W := landing K F J.fee J.reserve (.inl i)
  have hp : J.narrow*x.fires.val.card ≤ W + E + J.spare*D := by
    have hx := fee_work J hf hm h (K:=K) i; dsimp only [E,W,landing,Sum.elim_inl,x,D,P]; linarith only [hx]
  unfold budgetK; rw [← mul_div_assoc,le_div_iff₀ (show 0 < charge o (J.e+1) (K i).extent from Real.exp_pos _),hook,Poly.solo]
  set a := Poly.toll (fun _ : A × V => J.m0) x.fires
  have h2 : Poly.toll (fun _ => J.radius) x.fires = Real.exp (J.narrow * x.fires.val.card)*a := paid_marker J J.narrow x.fires
  change Poly.toll _ x.fires*‖x.value U‖*charge o (J.e+1) P ≤ Real.exp W * (Real.exp E*C i)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hc.2 U) (Real.exp_pos _).le) (Real.exp_pos _).le)
  change _ ≤ Real.exp W * (Real.exp E*(charge o _ P*a * _))
  rw [charged (o:=o) (J.e+1) J.spare,h2]
  have h3 : 0 ≤ a := (Poly.worth (fun _ => mul_pos J.pos_r (Real.exp_pos _)) _).le
  refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) h3)
    (norm_nonneg (x.value U))) (Real.exp_pos _).le).trans_eq ?_
  simp only [Real.exp_add,D,x,P,charge]; ring

variable {J}
variable {P : A × flame V → SourceAt G ζ} {D : A × flame V → ℂ}
variable (hP : Wells J P D Q)

private abbrev leave (o : BudgetPoint) (P : A × flame V → SourceAt G ζ) (D : A × flame V → ℂ) := fun i => Shift.fail (P i) (D i) o.threshold
private def budgetF (J : Change o m) (F : A × flame V → Refusal G ζ o.threshold) (i : A × flame V) := J.limit_c * Real.exp (-J.fee) / charge o (J.e+1) (F i).extent

include hP in
omit [Fintype κ] in
private lemma right_work (U : Config G n) (i : A × flame V) :
    Poly.price (fun _ => J.radius) (hook K (leave o P D) (.inr i) U) ≤
      Real.exp (landing K (leave o P D) J.fee J.reserve (.inr i))* budgetF J (leave o P D) i := by
  rw [hook,Poly.solo]; have he := hP.failed i
  unfold budgetF; change Poly.toll _ (P i).fires * ‖(leave o P D i).value U‖ ≤ Real.exp J.fee * (J.limit_c * _ / charge o (J.e+1) (P i).extent)
  rw [hP.room,hP.lit,← mul_div_assoc,le_div_iff₀ (show 0 < charge o (J.e+1) (Q i.1) from Real.exp_pos _)]
  rw [mul_comm J.limit_c,← mul_assoc,← Real.exp_add, add_neg_cancel,Real.exp_zero,one_mul]
  simp only [leave,Shift.fail]; split
  · rw [norm_zero,mul_zero, zero_mul]; exact J.first_c
  exact (mul_comm ..).le.trans ((by rw [← mul_assoc]; exact he) : _)

omit [DecidableEq A] in
private lemma once (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B) {c : ℝ} (hc : 0 ≤ c) (x : Site n) :
    ∑ i : (A × flame V),(if x∈Q i.1 then c else 0) ≤ ((2^m:ℕ):ℝ)*c := by
  have ht : Fintype.card (flame V) ≤ 2^m := fire_size.trans (pow_le_pow_right₀ (by norm_num) hm)
  rw [Fintype.sum_prod_type]
  by_cases hp : ∃ j,x∈Q j
  · obtain ⟨j,hj⟩ := hp
    rw [sum_eq_single j]
    · simp only [hj,↓reduceIte,sum_const,card_univ,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast ht) hc
    · intro b _ hb; simp only [if_neg (show x∉Q b from fun he => hb (Camp.pairwise h x b j he hj)),sum_const_zero]
    simp
  have hn (j : A) : x∉Q j := fun H => hp ⟨j,H⟩
  simp only [if_neg (hn _),sum_const_zero]; positivity

include hP in
private lemma warm (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B) {C : κ → ℝ}
    (hc : ∀ i,Lifted.pays o (K i) (fun _ => J.m0) (J.e+1+J.spare) (C i)) (ha : ∀ i : Site n,∑ j, (if i∈(K j).extent then C j else 0)≤J.hit) :
    ∃ c : Latch K (leave o P D) → ℝ, (∀ i,Lifted.pays o (merged K (leave o P D) i) (fun _ => J.radius) J.e (c i)) ∧
    ∀ x : Site n,(∑ i,(if x ∈(merged K (leave o P D) i).extent then c i else 0)) ≤ J.hail := by
  let F := leave o P D
  let f : κ ⊕ A × flame V → ℝ := Sum.elim (budgetK J K C) (budgetF J F)
  have hz := mul_nonneg J.first_c (Real.exp_pos (-J.fee)).le
  have hz' : 0 ≤ eK J := (Real.exp_pos _).le
  have hh i : 0 ≤ f i := by cases i with
  | inl i => exact div_nonneg (mul_nonneg hz' ((hc i).1)) (Real.exp_pos _).le
  | inr j => exact div_nonneg hz (Real.exp_pos _).le
  have hb i : (F i).extent=Q i.1 := hP.room i
  refine ⟨fun i => owed K F i f J.reserve J.e, fun i => pays K F J.fee J.reserve hh J.fee_cost J.reserve_cost (fun _ => J.pos_r) (fun j U => ?_) i, fun x => ?_⟩
  · cases j with
    | inl i => exact left_work J hb C i hm h (hc i) U
    | inr i => exact right_work hP U i
  have hv : Ac.Hit (area K F) o.B f (J.e+1) J.γ := by
    intro x; refine ⟨fun i => ?_,summable_of_hasFiniteSupport (Set.toFinite _),?_⟩
    · dsimp only; split
      · exact mul_nonneg (hh _) (Real.exp_pos _).le
      exact le_rfl
    let v := fun i => if x ∈ area K F i then f i * Real.exp ((J.e+1)*coverNumber o.B (area K F i)) else 0
    change ∑' i,v i ≤ _
    rw [tsum_fintype,Fintype.sum_sum_type]
    have he (i : κ) : v (.inl i) = eK J*(if x∈(K i).extent then C i else 0) := by
      by_cases hi : x∈(K i).extent
      · simp only [v, if_pos hi,f,Sum.elim_inl,budgetK,area,charge]; field_simp
      simp only [v,if_neg (show x∉area K F (.inl i) from hi),if_neg hi,mul_zero]
    have hk (i : A × flame V) : v (.inr i) = (if x∈Q i.1 then J.limit_c*Real.exp (-J.fee) else 0) := by
      unfold v area; simp only [Sum.elim_inr,hb,f,budgetF,charge]; split_ifs
      · field_simp
      rfl
    simp_rw [he,hk,← mul_sum]
    exact (add_le_add (mul_le_mul_of_nonneg_left (ha _) hz') (once hm h hz x)).trans J.force_hit
  exact held_over K F J.reserve hh hv J.base J.fits J.main x

private lemma rent (hP : Wells J P D Q) (hm : Fintype.card V ≤ m) (h : rearranged ζ Q o.B) {H : ι → SourceAt G ζ} {c : ι→ℝ}
    (he : ∀ i,if singled (H i).fires then (H i).pays o (fun _ => J.m1) J.e (c i) else (H i).pays o (fun _ => J.m0) (J.e+J.spare) (c i))
    (hl : ∀ i : A × V, ∑ j,(if ¬ singled (H j).fires ∧ i∈(H j).fires.val then c j else 0) ≤ J.wing)
    (hy : ∀ i : A × V, ∑ j,(if singled (H j).fires ∧ i∈(H j).fires.val then c j else 0) ≤ J.yard) :
    ∃ c : ι ⊕ (A × flame V) → ℝ,(∀ i,(Sum.elim H (fun i => Shift.reg (P i) (D i)) i).pays o (fun _ => J.radius) J.e (c i)) ∧
    ∀ x : A × V,∑ i, (if x ∈ (Sum.elim H (fun i => Shift.reg (P i) (D i)) i).fires.val then c i else 0) ≤ J.output := by
  let S := fun i => if singled (H i).fires then Real.exp (m*J.inside)*c i else Real.exp (-J.saving)*c i
  let Y := fun i => Shift.reg (P i) (D i)
  let c' : ι ⊕ (A × flame V) → ℝ := Sum.elim S (fun _ => J.limit_w)
  refine ⟨c',fun i => ?_,fun i => ?_⟩
  · cases i with
    | inl i =>
      have hx := he i; dsimp only [Sum.elim_inl,c',S]; split_ifs with hg
      · rw [if_pos hg] at hx; exact single_cost J hm (H i) (c i) hg hx
      rw [if_neg hg] at hx; exact mixed_cost J h hm (H i) (c i) hg hx
    | inr i =>
      change (Y i).pays o _ _ _
      refine ⟨J.first_w,fun U hU => ?_⟩; unfold Y Shift.reg; dsimp only; rw [hP.room,hP.lit]
      exact hP.restored _ _ ((hP.room i) ▸ (show Healthy o.threshold (P i).extent U from hU))
  have hh j : (if i∈(H j).fires.val then S j else 0)= Real.exp (-J.saving)*(if ¬ singled (H j).fires ∧ i ∈ (H j).fires.val then c j else 0)+
      Real.exp (m*J.inside)*(if singled (H j).fires ∧ i∈(H j).fires.val then c j else 0) := by
      by_cases h : singled (H j).fires <;> by_cases H' : i∈(H j).fires.val <;> simp [S,h,H']
  rw [Fintype.sum_sum_type]; simp_rw [c',Sum.elim_inl,Sum.elim_inr,hh,sum_add_distrib, ← mul_sum]
  rw [add_comm _ (∑ j : A × flame V, if i∈(Y j).fires.val then J.limit_w else 0)]
  refine (add_le_add ?_ (add_le_add (mul_le_mul_of_nonneg_left (hl _) (Real.exp_pos _).le) (mul_le_mul_of_nonneg_left (hy _) (Real.exp_pos _).le))).trans J.weather
  apply le_trans _ (once hm h J.first_w (ζ i)); apply sum_le_sum; intro p _; split_ifs with h1 h2 h2
  · exact le_rfl
  · exact False.elim (h2 ((hP.room p) ▸ ((P p).remembers i h1)))
  · exact J.first_w
  exact le_rfl

section
variable {D₀ : Rep G n}
theorem grant (J : Change D₀.p m) (hm : Fintype.card V ≤ m) (h : rearranged ζ Q D₀.p.B) (hP : Wells J P D Q)
    {H : ι → SourceAt G ζ} {K : κ → Lifted G ζ D₀.p.threshold} (R : Reception J H K) (hB : Background D₀ K) :
    Value.Notice D₀ ζ (fun U => Poly.pass (∑ i : A × flame V, Poly.send (P i).fires (D i))*dust D₀ (Sum.elim H P) K U)
      (fun _ => J.radius) J.e J.output J.hail := by
  obtain ⟨⟨c,hc,A,B⟩,⟨b,hb,M⟩⟩ := R
  refine ⟨_,_,inferInstance,inferInstance,Sum.elim H (fun i => Shift.reg (P i) (D i)), merged K (fun i => Shift.fail (P i) (D i) D₀.p.threshold),
    funext fun U => Shift.made D₀ K H P D U, fun i U=> (monogous K _ i U).trans (hB ..),⟨rent hP hm h hc A B, warm hP hm h hb M⟩⟩
end
end YM.Next.Rank.Dock
