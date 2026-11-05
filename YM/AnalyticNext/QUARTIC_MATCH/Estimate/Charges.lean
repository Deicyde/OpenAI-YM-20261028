import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Currency
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Slopes
import YM.Next.FREE_KERNELS.Gear
import YM.PREC.Pred

/-!
# Book from actual analytical assignments, not from commutative proxies for walks
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis
open scoped Topology ContDiff BigOperators
namespace Purse
variable {X Y Z E α ι : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z] [NormedAddCommGroup E]
    [NormedSpace ℝ X] [NormedSpace ℝ Y] [NormedSpace ℝ Z] [NormedSpace ℝ E]
    [Fintype α]

abbrev Jets (P : Purse ι α) (S : Finset ι) (d : ι→X) (f : α → X→Y) (x : X) (C : ℝ) :=
    Pays P S (fun i => bill S d (f i) x) C
variable {P : Purse ι α} {f : α→X→Y} {g : α→X→Z} {F : α→X→E} {u : α→X→Y}
  {x : X} {d : ι→X} {C D : ℝ} {S : Finset ι}
lemma Jets.adding (hf : ∀ i, ContDiffAt ℝ ω (f i) x) (hu : ∀ i, ContDiffAt ℝ ω (u i) x) (h : Jets P S d f x C) (q : Jets P S d u x D) :
    Jets P S d (fun i z => f i z+u i z) x (C+D) := by
  refine (h.plus q).under fun _ => ?_; dsimp only [Pi.add_apply]; rw [plus_rate _ _ (hf _) (hu _)]
lemma Jets.spend (h : Jets P S d f x C) (L : Y→L[ℝ] Z) (he : ∀ i, ContDiffAt ℝ ω (f i) x) {v : ℝ} (hp : 0 ≤ v) (hv : ∀ y, ‖L y‖ ≤ v*‖y‖) :
    Jets P S d (fun i => L ∘ f i) x (v*C) := h.repay hp fun i => by dsimp only; rw [left_price S d L (he i)]; exact hv _
lemma Jets.change_map (h : Jets P S d f x C) (L : Y→L[ℝ] Z) (he : ∀ i, ContDiffAt ℝ ω (f i) x) (hv : ∀ y, ‖L y‖ ≤ ‖y‖) :
    Jets P S d (fun i => L ∘ f i) x C := by
  rw [← one_mul C]; exact h.spend L he zero_le_one fun y => (hv y).trans_eq (one_mul _).symm
lemma Jets.rate (h : Jets P S d f x C) (r : ℝ) (he : ∀ i, ContDiffAt ℝ ω (f i) x) :
    Jets P S d (fun i z => r • f i z) x (|r| *C) := h.repay (abs_nonneg _) fun i => by
  change ‖bill S d (r • f i) x‖ ≤ _; rw [smul_price _ _ (he i), norm_smul]; rfl

lemma Jets.allotted {κ : Type*} (q : Finset κ) {E : κ→ℝ} (F : κ→α→X→Y)
    (hg : ∀ i∈q, ∀ j, ContDiffAt ℝ ω (F i j) x) (h : ∀ i∈q, Jets P S d (F i) x (E i)) :
    Jets P S d (fun i z => ∑ j∈q,F j i z) x (∑ j∈q, E j) := (Pays.gather q E h).under fun i => by
      dsimp only
      rw [Finset.sum_apply,sum_bill q S d (fun j => F j i)]
      exact fun j hj => hg j hj i

section product
variable [DecidableEq ι]
lemma Jets.pay (φ : Y→L[ℝ] Z→L[ℝ] E) (hc : ∀ x y, ‖φ x y‖ ≤ ‖x‖*‖y‖) (hf : ∀ i,
    ContDiffAt ℝ ω (f i) x) (hg : ∀ i, ContDiffAt ℝ ω (g i) x)
    (v w : Finset ι→ℝ) (h : ∀ T⊆S, Jets P T d f x (v T)) (q : ∀ T⊆S, Jets P T d g x (w T)) :
    Jets P S d (fun i z => φ (f i z) (g i z)) x (∑ T∈S.powerset, v T*w (S\T)) := by
  unfold Jets
  have he (T) (he : T⊆S) : P.Pays S (fun i => φ (bill T d (f i) x) (bill (S\T) d (g i) x)) (v T*w (S\T)) := by
    have hU := Pays.times (z:=fun i => φ (bill T d (f i) x) (bill (S\T) d (g i) x)) (h T he) (q (S\T) Finset.sdiff_subset) Finset.disjoint_sdiff (fun _ => hc ..)
    rwa [Finset.union_sdiff_of_subset he] at hU
  refine (Pays.gather S.powerset (fun T => v T*w (S\T)) (fun t ht => he t (Finset.mem_powerset.mp ht))).under fun i => ?_
  dsimp only; rw [Finset.sum_apply, account ..]
  exact hf _
  exact hg _

lemma Jets.priced (φ : Y→L[ℝ] Z→L[ℝ] E) (hc : ∀ x y, ‖φ x y‖ ≤ ‖x‖*‖y‖) (hf : ∀ i,
    ContDiffAt ℝ ω (f i) x) (hg : ∀ i, ContDiffAt ℝ ω (g i) x)
    (h : ∀ T⊆S, Jets P T d f x C) (q : ∀ T⊆S, Jets P T d g x D) (n : ℕ) (hn : S.card ≤ n) :
    Jets P S d (fun i z => φ (f i z) (g i z)) x ((2:ℝ)^n*(C*D)) := by
  apply (Jets.pay φ hc hf hg (fun _ => C) (fun _ => D) h q).mono
  rw [Finset.sum_const, Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) (mul_nonneg (h S fun _ he => he).1 (q S fun _ he => he).1)
end product
end Purse
end YM.AnalyticNext.QuarticMatch.Estimate
