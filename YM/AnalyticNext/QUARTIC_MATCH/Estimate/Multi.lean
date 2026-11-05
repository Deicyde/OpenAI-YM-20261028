import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Collective

/-!
# Chain rule on collective purchases
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch
open Progress.StationaryScenes Work.F03 YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
namespace Purse
variable {X Y E Z ι α β : Type} [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedAddCommGroup E]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] [NormedSpace ℝ E]
    [Fintype α] [Fintype β] [Nonempty β] [DecidableEq ι]

abbrev Many (P : Purse ι α) (S : Finset ι) (d : ι→X) (f : α→β→X→Y) (x : X) (C : ℝ) :=
    P.Spend S (fun i j => bill S d (f i j) x) C
variable {P : Purse ι α} {S : Finset ι} {f : α→β→X→Y} {g : α→β→X→Z} {x : X} {C D : ℝ} {d : ι→X}

omit [DecidableEq ι] in
lemma Many.edit (h : Many P S d f x C) (hg : ∀ i j,ContDiffAt ℝ ω (f i j) x) (A : Y→L[ℝ] Z) (hv : ∀ y, ‖A y‖ ≤ ‖y‖) :
    Many P S d (fun i j => A ∘ f i j) x C := h.change fun i j => by dsimp only; rw [left_price S d A (hg i j)]; exact hv _
lemma Many.pay (φ : Y→L[ℝ] Z→L[ℝ] E) (hc : ∀ x y, ‖φ x y‖ ≤ ‖x‖*‖y‖)
    (h : ∀ i j,ContDiffAt ℝ ω (f i j) x) (hp : ∀ i j,ContDiffAt ℝ ω (g i j) x)
    (v w : Finset ι→ℝ) (he : ∀ T⊆S, Many P T d f x (v T)) (ht : ∀ T⊆S, Many P T d g x (w T)) :
    Many P S d (fun i j z => φ (f i j z) (g i j z)) x (∑ u∈S.powerset,v u*w (S\u)) := by
  have hh (T : Finset ι) (hh : T⊆S) : P.Spend S (fun i j => φ (bill T d (f i j) x) (bill (S\T) d (g i j) x)) (v T*w (S\T)) := by
    have hk := Spend.times (u:=fun i j => φ (bill T d (f i j) x) (bill (S\T) d (g i j) x)) (he _ hh) (ht _ Finset.sdiff_subset) Finset.disjoint_sdiff
      (fun i _ => hc ..)
    rwa [Finset.union_sdiff_of_subset hh] at hk
  refine (Spend.finite S.powerset (fun i hi => hh i (Finset.mem_powerset.mp hi))).change ?_
  intro i j; simp only [Finset.sum_apply]; rw [account φ S d _ _ x (h i j) (hp i j)]
lemma Many.priced (φ : Y→L[ℝ] Z→L[ℝ] E) (hc : ∀ x y, ‖φ x y‖ ≤ ‖x‖*‖y‖)
    (h : ∀ i j, ContDiffAt ℝ ω (f i j) x) (g' : ∀ i j, ContDiffAt ℝ ω (g i j) x)
    (hP : ∀ T⊆S, Many P T d f x C) (hQ : ∀ T⊆S, Many P T d g x D) (n) (hp : S.card ≤ n) :
    Many P S d (fun i j z => φ (f i j z) (g i j z)) x (2^n*(C*D)) := by
  apply (Many.pay φ hc h g' (fun _ => C) (fun _ => D) hP hQ).mono
  rw [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hp) (mul_nonneg (hP _ fun _ he => he).1 (hQ _ fun _ he => he).1)

lemma adjoin_budget {i : ι} (hi : i∉S) (g : X→Y) (x) (h : ContDiffAt ℝ ω g x) (d : ι→X) :
    bill (insert i S) d g x=bill S d (Analysis.D (d i) g) x := by
  rw [counted hi d g x h]
  unfold bill
  rw [← Analysis.cons_inner (j:=S.card) (h.of_le le_top) (d i) (hook S d), Analysis.cons_jet (h.of_le le_top)]

lemma chain_bill {i : ι} (hi : i∉S) (g : X→Y) (x) (h : ContDiffAt ℝ ω g x) (d : ι→X) (F : Y→Z) (he : ContDiffAt ℝ ω F (g x)) :
    bill (insert i S) d (F ∘ g) x = ∑ T∈S.powerset,
      bill T d (fderiv ℝ F ∘ g) x (bill (insert i (S\T)) d g x) := by
  have hg : ContDiffAt ℝ ω (Analysis.D (d i) g) x := dSmooth h _ (by simp)
  have hh : ContDiffAt ℝ ω (fderiv ℝ F ∘ g) x := (he.fderiv_right (by simp)).comp _ h
  have ht : Analysis.D (d i) (F ∘ g) =ᶠ[𝓝 x] fun y => ContinuousLinearMap.id ℝ _ ((fderiv ℝ F ∘ g) y) (Analysis.D (d i) g y) := by
    filter_upwards [h.eventually (by simp), h.continuousAt.tendsto.eventually (he.eventually (by simp))] with y hy hu
    exact D_comp ((show ContDiffAt ℝ ω F (g y) from hu).differentiableAt (by simp)) ((show ContDiffAt ℝ ω g y from hy).differentiableAt (by simp))
  rw [adjoin_budget hi (F ∘ g) x (he.comp _ h),germ ht, account (ContinuousLinearMap.id ℝ _) _ _ _ _ _ hh hg]
  apply Finset.sum_congr rfl; intro j _; rw [adjoin_budget (show i∉ S\j by simp [hi]) g x h]; rfl

lemma group_price {u : ℕ} {S : Finset ι} (hf : ∀ i j, ContDiffAt ℝ ω (f i j) x) (F : Y→Z)
    (y : Y) (h : ContDiffAt ℝ ω F y) (hh : ∀ i j, f i j x=y) (hs : S.card=u+1)
    (C D : ℝ) (he : ∀ A⊆S, A.card ≤ u → P.Many A d f x C)
    (ht : ∀ A⊆S, A.card ≤ u → P.Many A d (fun i j => fderiv ℝ F ∘ f i j) x D) :
    P.Spend S (fun i j => bill S d (F ∘ f i j) x - fderiv ℝ F y (bill S d (f i j) x)) ((2:ℝ)^u*(D*C)) := by
  have hS : S.Nonempty := Finset.card_pos.mp (by omega)
  induction S using Finset.induction_on with
  | empty => simp_all
  | @insert i T hi ih =>
    have hv : T.card=u := by rw [Finset.card_insert_of_notMem hi] at hs; omega
    let W := T.powerset.erase ∅
    let t (A : Finset ι) (j : α) (k : β) :=
      bill A d (fderiv ℝ F ∘ f j k) x (bill (insert i (T\A)) d (f j k) x)
    have hb (A) (ha : A ∈ W) : P.Spend (insert i T) (t A) (D*C) := by
      obtain ⟨hb,hA⟩ := Finset.mem_erase.mp ha
      have hz : A ⊆ T := Finset.mem_powerset.mp hA
      have hh : A.card ≤ u := (Finset.card_le_card hz).trans_eq hv
      have h' : i ∉ A := Finset.notMem_mono hz hi
      have hw : (insert i (T\A)).card ≤ u := by
        rw [Finset.card_insert_of_notMem (by simp [hi])]; have hx := Finset.card_sdiff_add_card_eq_card hz; have hm := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hb); omega
      have H : P.Spend (A∪insert i (T\A)) (t A) (D*C) := Spend.times
        (ht A (hz.trans (Finset.subset_insert _ _)) hh) (he _ (Finset.insert_subset_insert _ Finset.sdiff_subset) hw) (by simp [h',Finset.disjoint_sdiff])
        (fun j k => ContinuousLinearMap.le_opNorm _ _)
      rwa [Finset.union_insert,Finset.union_sdiff_of_subset hz] at H
    refine Spend.mono (C:=∑ _A∈W,D*C) ?_ ?_
    · refine (Spend.finite _ hb).change fun j k => ?_
      rw [chain_bill hi _ x (hf j k) d F (by rw [hh]; exact h)]
      let a := ∑ l∈W, t l j k
      have hy : a + t ∅ j k=∑ A∈T.powerset, t A j k := Finset.sum_erase_add _ _ (by simp)
      have hu : t ∅ j k=fderiv ℝ F y (bill (insert i T) d (f j k) x) := by unfold t; rw [blank,Function.comp_apply,hh,Finset.sdiff_empty]
      change ‖(∑ A∈T.powerset,t A j k)-_‖ ≤ _
      rw [← hy,hu,add_sub_cancel_right]
      unfold a; simp only [Finset.sum_apply]; rfl
    rw [Finset.sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right
      (show (W.card:ℝ) ≤ (2:ℝ)^u from by exact_mod_cast (show W.card≤2^u by
        apply (Finset.card_le_card (Finset.erase_subset ..)).trans_eq; rw [Finset.card_powerset,hv])) (mul_nonneg (ht ∅ (by simp) (by simp)).1 (he ∅ (by simp) (by simp)).1)

/-- Before *sizes*. Also handles `ω` analytic implicit projections by lowering
orders. -/
theorem ordered (F : Y→Z) (y : Y) (h : ContDiffAt ℝ ω F y) (u : ℕ) (C : ℝ) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (ι α β X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [Fintype α] [Fintype β] [Nonempty β] [DecidableEq ι], ∀ (f : α→β→X→Y) (x d) (P : Purse ι α) (S : Finset ι), S.card ≤ u →
      (∀ i j, ContDiffAt ℝ ω (f i j) x) → (∀ i j,f i j x=y) → (∀ B⊆S,P.Many B d f x C) → P.Many S d (fun i j => F ∘ f i j) x D := by
  induction u generalizing Z with
  | zero =>
    refine ⟨‖F y‖,norm_nonneg _,?_⟩
    intro ι α β X _ _ _ _ _ _ f x d P S hs hF hh hp
    rw [Nat.le_zero,Finset.card_eq_zero] at hs; subst S; unfold Many
    simp_rw [blank,Function.comp_apply, hh]
    exact Spend.blank (norm_nonneg _) (fun _ _ => le_rfl)
  | succ u ih =>
    obtain ⟨C',hp,h₁⟩ := ih F h
    obtain ⟨K,hK,h₂⟩ := ih (fderiv ℝ F) (h.fderiv_right (by simp))
    let L := fderiv ℝ F y; let r := ‖L‖
    refine ⟨max C' (r*C+(2:ℝ)^u*(K*C)),le_trans hp (le_max_left ..),?_⟩
    intro ι α β X _ _ _ _ _ _ f x d P S hs hF hh hv
    rcases Nat.eq_or_lt_of_le hs with hx|hx
    · have he := fun A (he : A⊆S) (_ : A.card ≤ u) => hv A he
      have ha := group_price hF F y h hh hx C K he (fun i hi hj =>
        h₂ _ _ _ _ _ _ _ P i hj (fun i j => hF i j) hh (fun B hB => hv B (hB.trans hi)))
      let v (i : α) (j : β) := L (bill S d (f i j) x)
      have hm := ((hv S (@fun _ hx => hx)).rate (g:=v) (show 0 ≤ r from norm_nonneg _) (fun i j => L.le_opNorm _))
      refine ((hm.plus ha).mono (le_max_right ..)).change fun i j => ?_
      simp only [Pi.add_apply,v, L,add_sub_cancel]; rfl
    exact (h₁ ι α β X f x d P S (by omega) hF hh hv).mono (le_max_left ..)
/-- Also price the residual after taking the exact derivative term. -/
theorem leftover (F : Y→Z) (y : Y) (h : ContDiffAt ℝ ω F y) (u : ℕ) (C : ℝ) (hc : 0 ≤ C) :
    ∃ D : ℝ,0 ≤ D ∧ ∀ (ι α β X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X]
      [Fintype α] [Fintype β] [Nonempty β] [DecidableEq ι], ∀ (f : α→β→X→Y) (x d) (P : Purse ι α) (S : Finset ι), S.card = u+1 →
      (∀ i j,ContDiffAt ℝ ω (f i j) x) → (∀ i j,f i j x=y) → (∀ B⊆S,B.card ≤ u → P.Many B d f x C) →
      P.Spend S (fun i j => bill S d (F ∘ f i j) x - fderiv ℝ F y (bill S d (f i j) x)) D := by
  obtain ⟨D,he,hh⟩ := ordered (fderiv ℝ F) y (h.fderiv_right (by simp)) u C
  refine ⟨(2:ℝ)^u*(D*C),by positivity,?_⟩; intro ι α β X _ _ _ _ _ _ f x d P S hs hF hh' hx
  exact group_price hF F y h hh' hs _ _ hx fun i hi hk => hh _ _ _ _ _ _ _ P i hk hF hh'
    (fun B hB => hx B (hB.trans hi) ((Finset.card_le_card hB).trans hk))
end Purse
end YM.AnalyticNext.QuarticMatch.Estimate
