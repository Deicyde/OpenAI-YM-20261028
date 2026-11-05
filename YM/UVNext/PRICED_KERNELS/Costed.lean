import YM.Next.FREE_KERNELS.Signal
import YM.Next.SCHEDULE.Melt
import YM.Push.PRICE_COMPILER.Authors


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Analytic costs with vanishing jets → left link receipts

From uniform path costs through arbitrary pre-L orders (see `Scheduling.Wages.Path`),
a frequent downstream need will be derivative cost of a local analytic replacement
with known zeros through some Taylor order at flat. All measurements on ACTUAL
link arrays; even though `ContDiffBump` or other constructions on chart closure can
be used in the argument, don't replace the path expression or its germs on the group.
Foundational lemma for tipping + reaction to startup masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.PricedKernels
open Filter Set Function Lattice RG RG.Supply Wilson Precision Exterior Gauge Work.G07
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge}
section Link
variable {n : Side} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : Config G n → E} {g : Config G n → E →L[ℝ] F} {D : Directions G n → Prop} {Z : Config G n → Prop}
    {k j : ℕ} {C B : ℝ}
abbrev bill (k : ℕ) (D : Directions G n → Prop) (Z : Config G n → Prop) (C : ℝ) (f : Config G n → E) := LeftBound k D Z 1 C f
lemma bill.le (h : bill k D Z C f) (he : C ≤ B) : bill k D Z B f :=
    ⟨h.smooth,h.nonneg.trans he,fun l hl hD U hU => by simpa using! (le_trans (h.bound l hl hD U hU) (mul_le_mul_of_nonneg_right he (by positivity)))⟩
lemma first_mul (hx : LeftSmooth k g) (hy : LeftSmooth k f) (A : Directions G n) :
    leftDerivs (fun U => g U (f U)) [A] =
      fun U => (leftDerivs g [A] U) (f U) + (g U) (leftDerivs f [A] U) := by
  funext U
  change deriv _ 0 = _
  have he := ((hx.has (l:=[]) (Nat.zero_le _) U A).clm_apply (hy.has (l:=[]) (Nat.zero_le _) U A)).deriv
  simpa only [zero_smul,at_zero_increment] using! he

lemma lapply (hx : LeftSmooth k g) (hy : LeftSmooth k f) : LeftSmooth k fun U => g U (f U) := by
  induction k generalizing g f with
  | zero =>
    intro l hl U; rw [Nat.le_zero,List.length_eq_zero_iff] at hl; subst l
    exact (hx [] (Nat.zero_le _) U).clm_apply (hy [] (Nat.zero_le _) U)
  | succ j ih =>
    intro l hl U
    induction l using List.reverseRecOn with
    | nil => exact (hx [] hl U).clm_apply (hy [] hl U)
    | append_singleton l A _ =>
      simp only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] at hl
      rw [left_append,first_mul hx hy A]; exact ((ih (hx.inner_derivative A) (hy.truncate (Nat.le_succ _))).add
        (ih (hx.truncate (Nat.le_succ _)) (hy.inner_derivative A))) _ hl _

lemma bill.norm (h : bill k D Z C f) (l : List (Directions G n)) (hl : l.length ≤ k) (he : ∀ i∈l,D i) (U : Config G n) (hU : Z U) :
    ‖leftDerivs f l U‖ ≤ C := by simpa using h.bound l hl he U hU

lemma shrink (h : bill (k+1) D Z C f) (A : Directions G n) (he : D A) : bill k D Z C (leftDerivs f [A]) := by simpa using h.inner_derivative zero_le_one he

/-- Fee uniform over all sizes, using counting absorbed in op norms of small color space
only. -/
lemma bill.times (h : bill k D Z C f) (b : bill k D Z B g) : bill k D Z (2^k*B*C) (fun U => (g U) (f U)) := by
  have ht:=b.nonneg; have hr:=h.nonneg
  refine ⟨lapply b.smooth h.smooth,by positivity,?_⟩
  intro l hl he U hU; simp only [one_pow, mul_one]
  induction k generalizing f g l with
  | zero =>
    rw [Nat.le_zero,List.length_eq_zero_iff] at hl
    subst l; rw [pow_zero,one_mul]
    exact ((g U).le_opNorm (f U)).trans (mul_le_mul (b.norm [] le_rfl he U hU) (h.norm [] le_rfl he U hU) (norm_nonneg _) b.nonneg)
  | succ k ih =>
    induction l using List.reverseRecOn with
    | nil =>
      exact ((g U).le_opNorm (f U)).trans (mul_le_mul ((b.norm _ hl he U hU).trans (le_mul_of_one_le_left ht (one_le_pow₀ (by norm_num)))) (h.norm _ hl he U hU) (norm_nonneg _) (by positivity))
    | append_singleton l A _ =>
      simp only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] at hl
      simp only [List.mem_append,List.mem_singleton] at he
      have hA := he A (Or.inr rfl)
      have hs i hi:=he i (Or.inl hi)
      rw [left_append,first_mul b.smooth h.smooth A,left_add (lapply (b.smooth.inner_derivative A) (h.smooth.truncate (Nat.le_succ _)))
        (lapply (b.smooth.truncate (Nat.le_succ _)) (h.smooth.inner_derivative A)) hl]
      exact (norm_add_le ..).trans ((add_le_add (ih (h.truncate (Nat.le_succ _)) (shrink b A hA) l hl hs) (ih (shrink h A hA)
        (b.truncate (Nat.le_succ _)) l hl hs)).trans_eq (by rw [pow_succ]; ring))
end Link

section H
universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k m : ℕ} (φ : E → F) (hr : ContDiff ℝ ∞ φ) (he : ∀ i < k, iteratedFDeriv ℝ i φ 0=0)
include he

include hr
omit he in
lemma smooth_next : ContDiff ℝ ∞ (fderiv ℝ φ) :=
  (contDiff_succ_iff_fderiv.mp (by simpa using hr)).2.2 -- omitting he? 



omit he in
/-- Link first derivative chain, use repeatedly with fderiv tower. -/
lemma point_impact {n : Side} (f : Config G n → E) (h : LeftSmooth m f) (A : Directions G n) :
    leftDerivs (φ ∘ f) [A]=fun U => fderiv ℝ φ (f U) (leftDerivs f [A] U) := by
  funext U
  change deriv _ 0 = _
  have H := (((hr.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt 0 (h.has (l:=[]) (Nat.zero_le _) U A)).deriv
  simpa only [zero_smul, at_zero_increment] using! H

omit he in
lemma comp_pose {n : Side} (f : Config G n → E) (h : LeftSmooth m f) : LeftSmooth m (φ ∘ f) := by
  induction m generalizing F with
  | zero =>
    intro l hl U; rw [Nat.le_zero,List.length_eq_zero_iff] at hl
    subst l; exact hr.comp (h [] (Nat.zero_le _) U)
  | succ m ih =>
    intro l hl U
    induction l using List.reverseRecOn with
    | nil => exact hr.comp (h [] (Nat.zero_le _) U)
    | append_singleton l A _ =>
      simp only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] at hl
      rw [left_append,point_impact φ hr f h]
      -- callee smooth_next argument order check
      have hh := ih (fderiv ℝ φ) (smooth_next φ hr) (h.truncate (Nat.le_succ m))
      exact lapply hh (h.inner_derivative A) l hl U


end H
end YM.UVNext.PricedKernels
