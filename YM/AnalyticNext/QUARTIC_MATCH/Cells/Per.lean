import YM.AnalyticNext.QUARTIC_MATCH.Cells.Resolve

/-!
# Absolute periodization, exterior naturality

Read tensor PER ROOT. There's one translation factor when summing root upstairs,
not here. `echo` can use any lifts, retaining all winding translates. In
particular ∂-identities from geometry persist on the nose.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.BoxChain
open Lattice Exterior Function Finset Topology Laurent Filter
open scoped Topology BigOperators

variable {I : Type} {V : Type*} {R : Type*} [NormedAddCommGroup V]

/-- Shifts per slot. -/
def sway [AddCommGroup R] (w : I → Four R) (X : I → Cell R) := fun i => move (w i) (X i)


def tor (c : Side) (x : Cell ℤ) : Cell (Per c) := (wrap c x.1,x.2)
def rise (c : Side) (x : Cell (Per c)) : Cell ℤ := (lift x.1,x.2)

@[simp] lemma to_ground (c : Side) (x : Cell (Per c)) : tor c (rise c x)=x := by simp [tor,rise]
@[simp] lemma tor_move (c : Side) (x : Cell ℤ) (b : Cover) : tor c (move b x)=move (wrap c b) (tor c x) :=
    Prod.ext (map_add _ _ _) rfl

variable (c : Side) (i : I)

def sheets : AddSubgroup (I → Cover) where
  carrier := {F | (∀ j, wrap c (F j)=0) ∧ F i=0}
  zero_mem' := by simp
  add_mem' := fun {a b} ⟨ha,ht⟩ ⟨hb,hm⟩ => by simp [ha,ht,hb,hm]
  neg_mem' := fun {a} ⟨ha,ht⟩ => by simp [ha,ht]
lemma sheet_here (w : sheets c i) : w.val i=0 := w.property.2
lemma sheet_wrap (w : sheets c i) (j : I) : wrap c (w.val j)=0 := w.property.1 _

def echo (A : ArrayC I ℤ V) (X : I→ Cell ℤ) := ∑' w : ↥(sheets c i), A (sway w.val X)
lemma echo_step {A : ArrayC I ℤ V} (h : Cohere A) (X Y : I→Cell ℤ) (hx : tor c ∘ X = tor c ∘ Y) :
    echo c i A X=echo c i A Y := by
  let T j := (X j).1-(Y j).1
  let t := T i
  have ht j : wrap c (T j)=0 := by rw [map_sub, sub_eq_zero]; exact congr_arg Prod.fst (congr_fun hx j)
  let q : sheets c i := ⟨fun j => T j - t, fun j => by rw [map_sub,ht,show t=T i from rfl, ht,sub_zero], sub_self _⟩
  unfold echo
  rw [← Equiv.tsum_eq (Equiv.addRight q) (fun w : sheets c i => A (sway w.val Y))]
  refine tsum_congr fun w => ?_
  change _ = A (sway (w+q).val Y)
  rw [← h t (sway (w+q : sheets c i).val Y)]
  congr 1
  funext j
  apply Prod.ext
  · change (X j).1+w.val j=(Y j).1+(w.val j+ (T j-t))+t
    unfold T; abel
  change ((tor c ∘ X) j).2 = ((tor c ∘ Y) j).2
  exact congr_arg Prod.snd (congr_fun hx j)

def scene (A : ArrayC I ℤ V) (X : I → Cell (Per c)) := echo c i A (rise c ∘ X)
lemma scene_tor {A : ArrayC I ℤ V} (h : Cohere A) (X : I→Cell ℤ) :
    scene c i A (tor c ∘ X)=echo c i A X := by
  unfold scene; exact echo_step c i h _ _ (by ext1 j; simp)

variable {σ C : ℝ} {A : ArrayC I ℤ V}

section finite
variable [Fintype I]

def loads (x : I → Cover) : ℕ := ∑ i, size (x i)
lemma weight_loads (x : I → Cover) : loads x = size (fun i : I × Axis => x i.1 i.2) :=
    (Fintype.sum_prod_type (fun i : I × Axis => (x i.1 i.2).natAbs)).symm

lemma pays_all (h : 0 < σ) : RG.SumBudget (fun x : I → Cover => Real.exp (-σ*loads x))
    ((2*((1+σ)/σ))^(Fintype.card (I × Axis))) := by
  let E : (I → Cover) ≃ ((I × Axis) → ℤ) := (Equiv.curry I Axis ℤ).symm
  have he x : Real.exp (-σ*loads x)=Real.exp (-σ*size (E x)) := by rw [weight_loads]; rfl
  simp_rw [he]
  obtain ⟨hx,hg,hv⟩ := Laurent.Width.compactPay (α:=I × Axis) σ h
  exact ⟨fun i => hx _, E.summable_iff.mpr hg, (E.tsum_eq _).le.trans hv⟩

def shiftRate (I : Type) [Fintype I] (σ : ℝ) := σ/(Fintype.card I : ℝ)
lemma positive_rate (h : 0 < σ) (i : I) : 0 < shiftRate I σ := by
  have : Nonempty I := ⟨i⟩; exact div_pos h (by positivity)

lemma pricing_anchor (h : Pricing A σ C) (i : I) (X : I → Cell ℤ) :
    ‖A X‖ ≤ C * Real.exp (-shiftRate I σ * loads fun j => (X j).1-(X i).1) := by
  classical
  haveI : Nonempty I := ⟨i⟩
  let F j := size ((X j).1-(X i).1)
  obtain ⟨j,hj,hb⟩ := Finset.exists_max_image Finset.univ F univ_nonempty
  apply (h.each X j i).trans
  apply mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) h.cap
  have hm : ∑ i : I, F i ≤ Fintype.card I*F j := by
    convert! Finset.sum_le_sum (s:=Finset.univ) (fun i h => hb i h) using 1
    simp
  change -σ*(F j:ℝ) ≤ -(σ/(Fintype.card I:ℝ)) * ↑(∑ x,F x)
  have hg : ((∑ x,F x):ℝ) ≤ Fintype.card I*(F j:ℝ) := by exact_mod_cast hm
  have hf := div_mul_cancel₀ σ (show (Fintype.card I:ℝ)≠0 by positivity)
  rw [show -σ*↑(F j)= -(σ/Fintype.card I)*(Fintype.card I*(F j:ℝ)) by rw [← mul_assoc,neg_mul (σ/↑(Fintype.card I)),hf]]
  rw [Nat.cast_sum]; exact mul_le_mul_of_nonpos_left hg (neg_nonpos.mpr (positive_rate h.rate i).le)

lemma total_echo (h : Pricing A σ C) (X : I→Cell ℤ) : Summable fun w : sheets c i => ‖A (sway w.val X)‖ := by
  let E (w : sheets c i) : I → Cover := fun j => (sway w.val X j).1-(sway w.val X i).1
  have hx (w : sheets c i) j : E w j=(X j).1+w.val j-(X i).1 := by simp [E,move,sway,sheet_here]
  have he : Injective E := fun x y H => Subtype.ext <| funext fun j => by simpa only [hx,sub_left_inj,add_right_inj] using congr_fun H j
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => pricing_anchor h i _) ?_
  exact ((pays_all (I:=I) (positive_rate h.rate i)).2.1.mul_left C).comp_injective he
end finite

section legs
variable [NormedSpace ℝ V] [Fintype I] [DecidableEq I] [CompleteSpace V]

/-- Commute even with a change on the pivotal root. -/
theorem descend_lower (j : I) (h : Pricing A σ C) :
    lower j (scene c i A)=scene c i (lower j A) := by
  funext Y
  let X := rise c ∘ Y
  let x := (X j).1; let S := (X j).2
  have he : tor c ∘ X=Y := funext fun i => to_ground _ _
  have hs (b : Cell ℤ) : peek j Y (scene c i A) (tor c b)=echo c i A (update X j b) := by
    unfold peek; rw [← scene_tor c i h.same]
    congr 1; funext k; by_cases H : k=j <;> simp [H,X]
  have hx (b : Cover) (r : Finset Axis) (w : sheets c i) :
      peek j (sway w.val X) A (b+w.val j,r)=A (sway w.val (update X j (b,r))) := by
    unfold peek; congr 1; funext k; by_cases H : k=j <;> simp [H, sway, move]
  have ht (z : Axis) (w : sheets c i) : sect z (peek j (sway w.val X) A) (sway w.val X j) =
      if z∈ S then 0 else sign S z • (A (sway w.val (update X j (x-step z,insert z S)))-
        A (sway w.val (update X j (x,insert z S)))) := by
    rw [sect_at]; change (if z∈S then _ else _)=_
    split; · rfl
    change _ • (peek j _ _ (x+w.val j-step z, _) - peek j _ _ (x+w.val j, _)) = _
    rw [show x+w.val j-step z=x-step z+w.val j by abel,hx,hx]; rfl
  rw [lower_at]; unfold scene; change (∑ _ : Axis, _) = echo c i (lower j A) X
  unfold echo
  simp_rw [lower_at, ht]
  have hE (U : I→Cell ℤ) := (total_echo c i h U).of_norm
  rw [Summable.tsum_finsetSum]; swap
  · intro b d; split
    · exact summable_zero
    exact ((hE _).sub (hE _)).const_smul _
  apply Finset.sum_congr rfl; intro b _
  have hy : Y j=(wrap c x,S) := (congr_fun he j).symm
  change sect b (peek j Y (scene c i A)) (Y j)=_
  rw [sect_at,hy]; dsimp only; split
  · simp
  rw [show (wrap c x-step b, insert b S)=tor c (x-step b,insert b S) by simp [tor],
    hs,show (wrap c x, insert b S)=tor c (x,insert b S) from rfl, hs, tsum_const_smul'', (hE _).tsum_sub (hE _)]; rfl

end legs

variable [NormedSpace ℝ V] [CompleteSpace V]

theorem descend_list {n : ℕ} {A : ArrayC (Fin n) ℤ V} (i : Fin n) (h : Pricing A σ C) (s : List (Fin n)) :
    scene c i (solve s A)=solve s (scene c i A) := by
  induction s generalizing A C with
  | nil => rfl
  | cons a s ih =>
    change scene c i (solve s (lower a A)) = solve s (lower a (scene c i A))
    rw [descend_lower _ _ _ h]; exact ih (h.smaller a)

end YM.AnalyticNext.QuarticMatch.BoxChain
