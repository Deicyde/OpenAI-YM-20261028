import YM.AnalyticBridge.VERIFIED_RESET_STEP.Jets
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Gear
import YM.Push.LOCAL_SPLITTING.Calculus
import YM.Push.PRICE_COMPILER.Canonical



/-!
E:eq:FOE. Direction prices at any HEALTHY value; in fixed log coordinates
also need delay (price-weight-small on actual edges & value sup there, NOT
analytically continuing the price off domain). Only growth-tests at site,
NOT testing all these directions by summing componentwise E derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson RG Next.Foundations Push.Local
    MultiNext.SignedSource MultiNext.SignedSource.Mom AnalyticBridge.VerifiedReset
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {k m : ℕ}
    {f : Config G n → ℝ} {τ : ℝ} {U : Config G n} {x : Directions G n}

private lemma lift_regular (h : B.Regular X f) : B.Regular X (Complex.ofReal ∘ f) := by
  let L := Complex.ofRealCLM
  have he (U) (hh : Healthy B.threshold X U) : Chart B.order (Complex.ofReal ∘ f) U := L.contDiff.contDiffAt.comp _ (h.smooth U hh)
  exact ⟨fun _ _ hh => congrArg Complex.ofReal (h.sites _ _ hh),L.continuous.measurable.comp h.borel,
    fun _ _ => congrArg Complex.ofReal (h.symmetry _ _),he,fun U hh A _ hx => left_has A hx (he U hh)⟩
private lemma lift_sup (h : B.Regular X f) (hf : B.supBounds o X f τ) : B.supBounds o X (Complex.ofReal ∘ f) τ := by
  refine ⟨hf.1,fun U hU l hl hA => ?_⟩
  change ‖leftDerivs (Complex.ofRealCLM ∘ f) l U‖ ≤ τ; rw [left_linear Complex.ofRealCLM l (h.smooth U hU) hl]; exact (Complex.norm_real _).trans_le (hf.2 _ hU _ hl hA)

lemma along (h : B.Regular X f) (he : Healthy B.threshold X (increment U x)) : ContDiffAt ℝ (↑B.order) (f ∘ increment U) x :=
    Complex.reCLM.contDiff.contDiffAt.comp (g:= (Complex.reCLM)) x (Lyre.responsive U _ (lift_regular h) he)

private lemma casting (h : B.Regular X f) (he : Healthy B.threshold X (increment U x)) (hi : m ≤ B.order) (v : Fin m → Directions G n) :
    ‖iteratedFDeriv ℝ m (f ∘ increment U) x v‖ = ‖iteratedFDeriv ℝ m ((Complex.ofReal ∘ f) ∘ increment U) x v‖ := by
  rw [show iteratedFDeriv ℝ m ((Complex.ofReal ∘ f) ∘ increment U) x = _ from
    Complex.ofRealCLM.iteratedFDeriv_comp_left (along h he) (Nat.cast_le.mpr hi)]; exact (Complex.norm_real _).symm

structure Rights (G : Gauge) (k : ℕ) where
  fee : ℝ
  large : 1 ≤ fee
  born {n : Side} {m : ℕ} {f : Config G n → ℝ} {B : BudgetPoint} {X : Support n} {o : Site n}
    {τ : ℝ} (U : Config G n) (v : Fin m → Directions G n) (a : Fin m → ℝ) : m ≤ k → m ≤ B.order → B.Regular X f → B.supBounds o X f τ →
      Healthy B.threshold X U → (∀ i,Lyre.Sized (a i) (v i) B o) → ‖iteratedFDeriv ℝ m (f ∘ increment U) 0 v‖ ≤ (∏ i,a i)*fee*τ
  moves {n : Side} {m : ℕ} {f : Config G n → ℝ} {B : BudgetPoint} {X : Support n} {o : Site n}
    {τ : ℝ} (U : Config G n) (x : Directions G n) (v : Fin m → Directions G n) (a : Fin m → ℝ) : m ≤ k → m ≤ B.order → B.Regular X f → B.supBounds o X f τ →
      Healthy B.threshold X (increment U x) → (∀ e, needed X e → ‖x e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1) →
      (∀ i,Lyre.Sized (a i) (v i) B o) → ‖iteratedFDeriv ℝ m (f ∘ increment U) x v‖ ≤ (∏ i,a i)*fee*τ

lemma authority (G : Gauge) (k : ℕ) : Nonempty (Rights G k) := by
  choose A ha hA using fun m => Lyre.lyre m G
  choose W hw hW using fun m => Lyre.general m 1 G
  let C := ∑ i∈Finset.range (k+1), (A i + W i)
  have he i (hi : i ≤ k) : A i + W i ≤ C := Finset.single_le_sum (s:=Finset.range (k+1)) (f:=fun i => A i+W i) (fun i _ => by linarith [ha i,hw i]) (Finset.mem_range.mpr (by omega))
  refine ⟨C, by linarith [he 0 (Nat.zero_le k),ha 0,hw 0], fun U v a hm hi h hf hx hv => ?_,fun U x v a hm hi h hf hx he' hv => ?_⟩
  · have ht := casting h (show Healthy _ _ (increment U 0) from (at_zero U).symm ▸ hx) hi v
    rw [ht]; refine (hA _ _ _ _ _ _ U _ v a hi hx (lift_regular h) (lift_sup h hf) hv).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
      (Finset.prod_nonneg (fun i _ => (hv i).1))) hf.1)
    exact le_trans (le_add_of_nonneg_right (zero_le_one.trans (hw _))) (he _ hm)
  rw [casting h hx hi v]; refine (hW _ _ _ _ _ x _ U _ v a hi (lift_regular h) hx (lift_sup h hf) he' hv).trans ?_
  rw [mul_comm _ (∏ i, a i)]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (le_trans (le_add_of_nonneg_left (zero_le_one.trans (ha _))) (he _ hm)) (Finset.prod_nonneg (fun i _ => (hv i).1))) hf.1
end YM.PhysicalNext.JointLoad.Heir
