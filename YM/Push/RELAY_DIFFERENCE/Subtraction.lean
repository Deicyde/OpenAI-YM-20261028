import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.Regular
import YM.Work.B04

/-!
# Exact signed subtraction at Jma representations

Pre-mask regular payload subtraction only *when support labels agree* (at
the corresponding regular address). Otherwise retain both supports and
use both masks. Mark coefficients use the unmodified vacuum label index
(common H, including inventory/coverage, scalar and likelihood conventions).
Don't try to describe discrepancy size by adding the two separate budget
propagations past birth. A triangle bound here is for initial/absolute
budgets and identities of sums, NOT a discrepancy propagation estimate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.RelayDifference
open Function Set Filter MeasureTheory Extraction Wilson RG Labels Lattice Cells Source
  Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators
variable {n : Side} {G : Gauge} {e : ℕ} {F : Labels.Frame G e}

/-! ### Address surgery needed by exact subtraction -/

def splitCode {X : Type*} (a b : ℕ → X) (i : ℕ) : X := Sum.elim a b (Equiv.natSumNatEquivNat.symm i)
def primaryCode (i : ℕ) := Equiv.natSumNatEquivNat (Sum.inl i)
def extraCode (i : ℕ) := Equiv.natSumNatEquivNat (Sum.inr i)
@[simp] lemma split_primary {X : Type*} (a b : ℕ → X) (i : ℕ) : splitCode a b (primaryCode i)=a i := by simp [splitCode,primaryCode]
@[simp] lemma split_extra {X : Type*} (a b : ℕ → X) (i : ℕ) : splitCode a b (extraCode i)=b i := by simp [splitCode,extraCode]
lemma both_codes {s : ℕ → Prop} (h : ∀ i, s (primaryCode i)) (H : ∀ i, s (extraCode i)) : ∀ i, s i := by
  intro i; obtain ⟨j,rfl⟩ := Equiv.natSumNatEquivNat.surjective i
  cases j; exacts [h _,H _]

private lemma paired_sum {X : Type*} [NormedAddCommGroup X] (f : ℕ → X)
    (hp : Summable (fun i => f (primaryCode i))) (hq : Summable (fun i => f (extraCode i))) :
    Summable f ∧ (∑' i,f i) = ∑' i,(f (primaryCode i)+f (extraCode i)) := by
  let e := Equiv.natSumNatEquivNat
  refine ⟨e.summable_iff.mp (Summable.sum _ hp hq),?_⟩
  rw [←e.tsum_eq,Summable.tsum_add hp hq]
  exact @Summable.tsum_sum ℕ ℕ _ _ _ _ _ (fun i => f (e i)) hp hq

private lemma paired_budget {a b f : ℕ → ℝ} {c : ℝ} (h : SumBudget (fun i => a i+b i) c)
    (hg : ∀ i,0≤f i) (he : ∀ i,f (primaryCode i)+f (extraCode i)=a i+b i) : SumBudget f c := by
  have hp : Summable (fun i => f (primaryCode i)) := h.2.1.of_nonneg_of_le (fun i => hg _) fun i => by
    rw [←he]; exact le_add_of_nonneg_right (hg _)
  have hq : Summable (fun i => f (extraCode i)) := h.2.1.of_nonneg_of_le (fun i => hg _) fun i => by
    rw [←he]; exact le_add_of_nonneg_left (hg _)
  obtain ⟨ha,hb⟩ := paired_sum f hp hq
  refine ⟨hg,ha,?_⟩; rw [hb]; simp_rw [he]; exact h.2.2

lemma add_budget {ι : Type*} {a b : ι → ℝ} {u v : ℝ} (h : SumBudget a u) (H : SumBudget b v) :
    SumBudget (fun i => a i+b i) (u+v) :=
  ⟨fun i => add_nonneg (h.1 i) (H.1 i),h.2.1.add H.2.1,(h.2.1.tsum_add H.2.1).le.trans (add_le_add h.2.2 H.2.2)⟩

def combine (P Q : Coefficient F n) : Coefficient F n :=
    { x := P.x-Q.x
      support := splitCode P.support Q.support
      regular := splitCode
        (fun i => if P.support i = Q.support i then P.regular i - Q.regular i else P.regular i)
        (fun i => if P.support i = Q.support i then 0 else -Q.regular i)
      forced := P.forced-Q.forced }

variable {P Q : Coefficient F n} {o : Site n} {H : Hol G} {R : Rep G n}

private lemma pi_sub {f g : Config G n → ℂ} (h : H.PiVanish e o f) (hp : H.PiVanish e o g) : H.PiVanish e o (f-g) := by
  intro J
  obtain ⟨ha,hb⟩ := h J
  obtain ⟨ht,hv⟩ := hp J
  refine ⟨ha.sub ht,fun k hk => ?_⟩
  have hl : (k : WithTop ℕ∞) ≤ (e : WithTop ℕ∞) := Nat.cast_le.mpr hk
  simp only [Pi.sub_apply]
  rw [iteratedDeriv_fun_sub (ha.of_le hl) (ht.of_le hl), hb k hk,hv k hk, sub_self]

private lemma pi_zero : H.PiVanish e o (0 : Config G n → ℂ) := by
  intro J; exact ⟨contDiffAt_const,fun k hk => by
    change iteratedDeriv k (0:ℝ→ℂ) 0 = 0; simp⟩

lemma combo_format (hP : P.Format o H R) (hQ : Q.Format o H R) : (combine P Q).Format o H R := by
  let D := combine P Q
  have hs : ∀ i, R.p.Regular (D.support i) (D.regular i) ∧ o∈D.support i ∧ D.regular i 1=0 ∧
      (Nonwrapping (D.support i) o → H.PiVanish e o (D.regular i)) := by
    refine both_codes (fun i => ?_) (fun i => ?_)
    · simp only [D, combine, split_primary]
      split_ifs with he
      · have he' := hP.smooth i
        rw [he] at he' ⊢
        exact ⟨regular_sub he' (hQ.smooth i),hQ.origin i,by simp [hP.identity_null i,hQ.identity_null i],fun hb =>
          pi_sub (hP.projects i (he ▸ hb)) (hQ.projects i hb)⟩
      exact ⟨hP.smooth i,hP.origin i,hP.identity_null i,hP.projects i⟩
    simp only [D, combine, split_extra]
    split_ifs with he
    · exact ⟨by simpa using regular_smul 0 (hQ.smooth i),hQ.origin i,rfl, fun _ => pi_zero⟩
    refine ⟨by simpa using regular_smul (-1) (hQ.smooth i),hQ.origin i,?_,?_⟩
    · simp only [Pi.neg_apply,hQ.identity_null,neg_zero]
    intro ha
    simpa only [zero_sub] using (pi_sub pi_zero (hQ.projects i ha))
  refine ⟨fun i => (hs i).1,fun i => (hs i).2.1,fun i => (hs i).2.2.1,fun i => (hs i).2.2.2,?_,?_,?_,?_,?_⟩
  · intro i U hi
    by_cases h:P.forced i U≠0
    · exact hP.forcing _ _ h
    exact hQ.forcing _ _ fun he => hi (by simp [combine,not_not.mp h,he])
  · intro i hi; by_cases h:P.forced i≠0
    · exact hP.carried _ h
    exact hQ.carried _ fun he => hi (by simp [combine,not_not.mp h,he])
  · exact fun i k U => congr_arg₂ (· - ·) (hP.invariant i k U) (hQ.invariant i k U)
  · exact fun i U V h t => congr_arg₂ (· - ·) (hP.supported i U V h t) (hQ.supported i U V h t)
  intro i; exact (hP.borel i).sub (hQ.borel i)

lemma combo_cap (hP : P.Format o H R) (hQ : Q.Format o H R) {κ p q : ℝ}
    (h : P.remBound o R κ p) (hp : Q.remBound o R κ q) : (combine P Q).remBound o R κ (p+q) := by
  obtain ⟨a,b,ha,hb,hW,hκ,E,F⟩ := h
  obtain ⟨a',b',ha',hb',hW',-,E',F'⟩ := hp
  refine ⟨a+a',b+b',add_nonneg ha ha',add_nonneg hb hb',by linarith, hκ,?_,?_⟩
  · obtain ⟨A,hA,hS⟩ := E
    obtain ⟨B,hB,hU⟩ := E'
    let X := splitCode
      (fun i => if P.support i = Q.support i then A i+B i else A i)
      (fun i => if P.support i = Q.support i then 0 else B i)
    let D := combine P Q
    have hx : ∀ i, R.p.supBounds o (D.support i) (D.regular i) (X i) := by
      refine both_codes (fun i => ?_) (fun i => ?_)
      · simp only [D,X,combine,split_primary]
        split_ifs with he
        · exact bound_sub (hP.smooth i) (he ▸ hQ.smooth i) (hS i) (he ▸ hU i)
        exact hS _
      simp only [D,X,combine,split_extra]
      split_ifs with he
      · simpa using bound_smul 0 (hU i)
      simpa using bound_smul (-1) (hU i)
    refine ⟨X,paired_budget (add_budget hA hB) (fun i => mul_nonneg (Real.exp_pos _).le (hx i).1) ?_,hx⟩
    intro i
    simp only [X,combine,split_primary,split_extra]
    split_ifs with he
    · rw [he]; unfold BudgetPoint.mass; ring
    rfl
  obtain ⟨A,hA,hS⟩ := F
  obtain ⟨B,hB,hU⟩ := F'
  refine ⟨fun i => A i+B i,?_,fun i => ⟨add_nonneg (hS i).1 (hU i).1,fun U => (norm_sub_le ..).trans
    (add_le_add ((hS i).2 U) ((hU i).2 U))⟩⟩
  simpa only [BudgetPoint.mass,mul_add] using add_budget hA hB

private lemma mask_sub (t : ℝ) (X : Support n) (f g : Config G n → ℂ) (U : Config G n) :
    masked t X (f-g) U=masked t X f U-masked t X g U := by
  by_cases h:Healthy t X U <;> simp [h]

private lemma ray_line (P Q : Coefficient F n) (R : Rep G n) (i : ℕ) (U : Config G n) :
    (combine P Q).maskedTerm R (primaryCode i) U + (combine P Q).maskedTerm R (extraCode i) U =
        P.maskedTerm R i U-Q.maskedTerm R i U := by
  simp only [combine,Coefficient.maskedTerm,split_primary,split_extra]
  by_cases hw : Healthy R.p.threshold (Q.support i) U <;> split_ifs with he <;>
    simp [he,hw,sub_eq_add_neg]

private lemma exponential_sub (hP : P.Format o H R) (hQ : Q.Format o H R) {κ p q : ℝ}
    (ha : P.remBound o R κ p) (hb : Q.remBound o R κ q) (S : SectionData F) (U : Config G n) :
    (combine P Q).exponentialEntry o S R U=P.exponentialEntry o S R U-Q.exponentialEntry o S R U := by
  let D := combine P Q
  have hc := ((Coefficient.regular_series (combo_cap hP hQ ha hb)).summable U)
  let f : ℕ → ℂ := fun i => D.maskedTerm R i U
  change Summable f at hc
  have ht : Injective primaryCode := Equiv.natSumNatEquivNat.injective.comp Sum.inl_injective
  have hh : Injective extraCode := Equiv.natSumNatEquivNat.injective.comp Sum.inr_injective
  have he : (∑' i, D.maskedTerm R i U)= (∑' i,P.maskedTerm R i U)-(∑' i,Q.maskedTerm R i U) := calc
    _ = ∑' i,(D.maskedTerm R (primaryCode i) U + D.maskedTerm R (extraCode i) U) :=
      (paired_sum f (hc.comp_injective ht) (hc.comp_injective hh)).2
    _ = ∑' i,(P.maskedTerm R i U-Q.maskedTerm R i U) := tsum_congr fun i => ray_line P Q R i U
    _ = _ := Summable.tsum_sub ((Coefficient.regular_series ha).summable U) ((Coefficient.regular_series hb).summable U)
  have hg (v w : F.Coeff) : S.places (v-w) o = S.places v o-S.places w o := by
    funext z; change S.evaluate _ _= _
    exact congr_fun (map_sub (S.eval_linear.mk' _) v w) _
  unfold Coefficient.exponentialEntry
  rw [show _ = _ from he,combine,map_sub, map_sub,hg, mask_sub]; simp only [Pi.sub_apply]; abel

private lemma mark_sub (P Q : Coefficient F n) (R : Rep G n) (i : Finset ℕ) (U : Config G n) :
    (combine P Q).marked R i U=P.marked R i U-Q.marked R i U := by
  unfold Coefficient.marked
  split_ifs <;> simp only [combine,Pi.sub_apply,sub_mul,Finset.sum_sub_distrib,sub_self]

/-- Same vocabulary and same representation parameters. Summable on full
configuration space. Not a conditional-expectation subtraction of normalized
fields at different cutoffs! -/
theorem combo_density (hP : P.Format o H R) (hQ : Q.Format o H R) {κ p q σ c Λ δ w : ℝ}
    (h : P.remBound o R κ p) (hp : Q.remBound o R κ q) (hR : R.Lawful σ c Λ δ w) (S : SectionData F) :
    (combine P Q).density o S R = P.density o S R - Q.density o S R := by
  funext U
  simp only [Coefficient.density, exponential_sub hP hQ h hp,mark_sub,Pi.sub_apply]
  rw [Summable.tsum_sub ((Coefficient.marked_series hR h).summable U) ((Coefficient.marked_series hR hp).summable U)]
  ring
end YM.Push.RelayDifference
