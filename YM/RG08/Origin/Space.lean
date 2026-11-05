import YM.RG08.Origin.Rising

/-! # Derivations and exponential rule coefficientwise -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Finset Filter Analysis
open scoped Topology ContDiff
variable {X ι : Type}

section songs
private lemma current_unique {M V U B : Scroll (Psalm X)} (hU : countG U=B+dancing (countG M) U) (hV : countG V=B+dancing (countG M) V) (h : Muted _ U) (hg : Muted _ V) : U=V := by
  funext n i; induction i using Nat.caseStrongRecOn generalizing n with
  | zero => rw [h n,hg n]
  | ind i ih =>
    apply smul_right_injective _ (show (↑(i+1 : ℕ) : ℝ)≠0 by positivity)
    dsimp only; rw [Nat.cast_smul_eq_nsmul,Nat.cast_smul_eq_nsmul]; change countG U n _=countG V n _; rw [hU,hV]; simp only [Pi.add_apply,add_right_inj]
    exact dance_quiet _ _ _ (muted_counts M) (fun j hj m => ih j (Nat.lt_succ_iff.mp hj) m) n
-- phrase using rising exponential, apply `current_unique`.
lemma rhyme_t (F : Scroll (Psalm X)) (hp : Muted _ F) : countT (priori F)=dancing (countT F) (priori F) := by
  apply current_unique (B:=dancing (countT (countG F)) (priori F)) (M:=F)
  · rw [counters, (rhythm_exp _).2,countTn]
  · rw [countGn, (rhythm_exp _).2,counters, ← dance_rotate, ← dance_rotate,dance_sym (countT F)]
  · intro n; rw [countT,priori_zero,ingr,if_neg,smul_zero]; omega
  exact dance_left_muted _ _ fun i=> by rw [countT,hp (i+1),smul_zero]
end songs
variable [Fintype X]
section D
variable (u : X → ℝ) {F H : Scroll (Psalm X)}
lemma touring (h : Fluid F) : Fluid (countG F) := fun n e=> by
  change ContDiff ℝ ω (e • F n e); rw [← Nat.cast_smul_eq_nsmul ℝ]; exact ContDiff.const_smul (↑e:ℝ) (h n e)

def sway (u : X → ℝ) (F : Scroll (Psalm X)) : Scroll (Psalm X) := fun n e=> Analysis.D u (F n e)
lemma sway_fluid (h : Fluid F) : Fluid (sway u F) := fun n e=> dune _ (h n e)
lemma Dpast (f : ι→Psalm X) (s : Finset ι) (h : ∀ i∈s,ContDiff ℝ ω (f i)) : Analysis.D u (∑ i∈s,f i)=∑ i∈s, Analysis.D u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [D,funext_iff]
  | insert i s hi ih =>
    have hs j hj:= h j (mem_insert_of_mem (s:=s) hj)
    rw [sum_insert hi,sum_insert hi,Daddition _ (h i (mem_insert_self ..)) ((show ContDiff ℝ ω (∑ j∈s,f j) from ?_)), ih hs]
    rw [show (∑ j∈s,f j)=(fun v=> ∑ j∈s,f j v) from funext fun v=> Finset.sum_apply v ..]; exact ContDiff.sum hs
lemma sway_dance (hf : Fluid F) (hg : Fluid H) : sway u (dancing F H)= dancing (sway u F) H+dancing F (sway u H) := by
  funext n e
  have he i j : ContDiff ℝ ω (F (i:ℕ×ℕ).1 (j:ℕ×ℕ).1 * H i.2 j.2) := (hf _ _).mul (hg _ _)
  have hu b : ContDiff ℝ ω (∑ a∈wheel e,F (b : ℕ×ℕ).1 a.1*H b.2 a.2) := by
    let f a := F b.1 (a : ℕ×ℕ).1 * H b.2 a.2
    rw [show (∑ a∈wheel e,f a)=(fun v=> ∑ a∈wheel e, f a v) from funext fun v=>Finset.sum_apply v ..]; exact ContDiff.sum fun i _=>he b i
  rw [sway,dancing,Dpast _ _ _ (fun i _=>hu i)]; simp_rw [Dpast _ _ _ (fun i _=> he _ i),Dproduct _ (hf _ _) (hg _ _),sum_add_distrib]; rfl
lemma sway_count (h : Fluid F) : sway u (countG F)=countG (sway u F) := by
  funext n e; change Analysis.D u (e • F n e)= e • Analysis.D u (F n e); rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ,DscaleL _ _ (h n e)]
lemma sway_exp (h : Fluid F) (hp : Muted _ F) : sway u (priori F)=dancing (sway u F) (priori F) := by
  apply current_unique (M:=F) (B:=dancing (sway u (countG F)) (priori F))
  · rw [← sway_count u (priori_fluid h), (rhythm_exp _).2, sway_dance u (touring h) (priori_fluid h)]
  · rw [countGn,(rhythm_exp _).2,sway_count u h, ← dance_rotate, ← dance_rotate,dance_sym (sway u F)]
  · intro n; rw [sway,priori_zero]; unfold ingr; split; ·    funext x; simp [D]
    funext x; simp [D]
  exact dance_left_muted _ _ (fun i=> by rw [sway,hp i];    funext x; simp [D])
end D
end YM.RG08
