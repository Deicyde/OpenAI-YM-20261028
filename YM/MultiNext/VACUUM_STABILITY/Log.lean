import YM.MultiNext.VACUUM_STABILITY.Deletion
import YM.MultiNext.VACUUM_STABILITY.WordTest

set_option warningAsError false

/-!
# Uniform ordinary log conversion, multi-anchor and real-germ receipts

Exact statement holding on the actual finite tori uniformly at every evaluation (no restriction
on source count; `u` the realized scalar letters). For
use INSIDE a step; uses reserves in addition to the desired rate; not a loss allowed on each
successive step of the trajectory. Replaces graph proof with true convergent log via Deletion.
-/

set_option autoImplicit false
noncomputable section

namespace YM.Multi.Vacuum.Cluster
open RG Lattice Wilson Filter Finset Function MeasureTheory Text Cluster Syllable Corona Jets Hits
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical

variable {I : Type} {n : Side} {G : Gauge}

/-- Surcharge uniform in period & number of input letters. -/
def logPrice (P : BudgetPoint) := Hits.toll P.B * (baseFee P * 2)

lemma logPrice_pos (P : BudgetPoint) : 0 < logPrice P := mul_pos (Hits.toll_pos _) (mul_pos (base_pos _) (by norm_num))

namespace Chorus
variable (D : Chorus I n)

-- expose true root of tape line
abbrev Root (D : Chorus I n) : Type := D.tune.address

def pole (i : Root D) : Site n := Sigma.fst (show Σ x, (D x).address from i)

lemma poles (X : I → Support n) (M : ℕ) (h : ∀ x, (D x).Peaked X M x) (i : Root D) :
    D.pole i ∈ (D.tune.line i).ground X ∧ coverNumber M ((D.tune.line i).ground X) ≤ (D.tune.line i).bill X M :=
  h i.1 i.2

/-- The log is small at every possible root, incl roots not visited first in `peel`. -/
lemma root_budget (X : I → Support n) (P : BudgetPoint) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    {f : I → ℝ} (hF : ∀ i, 0 ≤ f i) (h : ∀ x, (D x).Peaked X P.B x) (hg : ∀ x,
      (D x).Fund (cost X P.B (a+6) f) (2*c)) : Ac.Hit (fun i => (D.tune.line i).ground X) P.B
    (fun i => charges X P f (D.tune.line i)) a (logPrice P*c) := by
  have he (i) : 0 ≤ charges X P f (D.tune.line i) := mul_nonneg ((D.tune.line i).weight_nonneg hF) <|
    pow_nonneg (zero_le_one.trans (rate_hi ..)) _
  have ht : 0 ≤ baseFee P := (base_pos _).le
  have hs : 0 ≤ baseFee P*(2*c) := mul_nonneg ht (mul_nonneg (by norm_num) hc)
  have hP x : SumBudget (fun i => charges X P f ((D x).line i) * Real.exp ((a+5)*((D x).line i).bill X P.B))
      (baseFee P*(2*c)) := by
    have hn (i : (D x).address) : 0 ≤ charges X P f ((D x).line i) := he (show Root D from Sigma.mk x i)
    refine Absolute.compare (permit_mul (hg x) ht) (fun i => mul_nonneg (hn i) (Real.exp_pos _).le) fun i => ?_
    let w := (D x).line i
    unfold charges cost
    change w.weight f * _ * _ ≤ _
    apply le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (annual P _) (w.weight_nonneg hF))
      (Real.exp_pos _).le)
    apply le_of_eq
    rw [Syllable.weight_expansion]
    change w.weight f * (baseFee P * Real.exp _) * _ = _ * (w.weight f * Real.exp _)
    let s := (w.bill X P.B:ℝ)
    rw [show (a+6)*s=s+(a+5)*s by ring,Real.exp_add]; ring
  unfold logPrice; rw [mul_assoc,mul_assoc (baseFee _)]
  refine Hits.everyone (o:=D.pole) ha hs he _ (fun i => (D.poles X _ h i).1) (fun i => (D.poles X _ h i).2) ?_
  intro x; let t := fun y => if y=x then baseFee P*(2*c) else 0
  have hy : SumBudget t (baseFee P*(2*c)) := by
    refine ⟨?_,(hasSum_fintype _).summable,?_⟩
    · intro i; unfold t; split; exact hs; exact le_rfl
    rw [tsum_fintype]; simp [t]
  -- sigma addressing, cost booked per root
  refine Absolute.bundles hy fun i => ?_
  by_cases hx : i=x
  · rw [hx] at *
    simpa only [t,pole,tune,Text.bind,if_true] using hP x
  simp only [pole,tune,Text.bind,t,hx,if_false]; simp [SumBudget]

/-- Missing clusters under a restriction detected by the *same tape*, so the forced
exclusions in the next merger are valid at value level. -/
lemma limited (X : I → Support n) (hn : ∀ i, (X i).Nonempty) (R : Support n)
    (H : Peeling X univ ∅ D) (P : BudgetPoint) {a c : ℝ} {f : I → ℝ} (hF : Thin X P.B a f c)
    (u : I → ℂ) (hh : ∀ i, ‖u i‖ ≤ f i) : BulkGas.Z X R u =
    Complex.exp (∑' i, if (D.tune.line i).ground X ⊆ R then (D.tune.line i).eval u else 0) := by
  let q i := if X i ⊆ R then u i else 0
  have he i : ‖q i‖ ≤ f i := by
    unfold q; split
    · exact hh i
    rw [norm_zero]; exact hF.val _
  have hv := D.finances _ H.waits (mul_nonneg (by norm_num) hF.sane) (H.affordable _ _ _ _ hF)
  rw [BulkGas.restrict, H.equality P.B a f c hF q he, BulkGas.vacant X hn q,mul_one,←D.tunes hv (fun i => (he i).trans (hF.enlarges i))]
  unfold Text.lineSum; exact congrArg Complex.exp (tsum_congr fun i => limit_range ..)

lemma earned (X : I → Support n) (R : Support n) (H : Peeling X univ ∅ D) (F : I → Config G n → ℂ)
    (o : I → Site n) (ho : ∀ i, o i ∈ X i) (P : BudgetPoint) (hr : ∀ i, P.Regular (X i) (F i))
    {a c : ℝ} (ha : 0 ≤ a) {f : I → ℝ} (hh : Thin X P.B (a+6) f c)
    (hF : ∀ i, P.supBounds (o i) (X i) (F i) (f i)) :
    let Y i := (D.tune.line i).ground X
    let E i := stanza F (D.tune.line i)
    let g i := charges X P f (D.tune.line i)
    (∀ i, P.Regular (Y i) (E i) ∧ ∀ x ∈ Y i, P.supBounds x (Y i) (E i) (g i)) ∧
      Ac.Hit Y P.B g a (logPrice P*c) ∧
      ∀ U, BulkGas.Z X R (fun i => masked P.threshold (X i) (F i) U) =
        Complex.exp (∑' i, if Y i ⊆ R then masked P.threshold (Y i) (E i) U else 0) := by
  intro Y E g
  have he i := D.poles X _ (H.roots P.B) i
  refine ⟨fun i => ⟨stanza_regular X F P hr _, stanza_bound X F P hr o ho f hF _ (he i).2⟩,
    D.root_budget X P ha hh.sane hh.val (H.roots P.B) (H.affordable _ _ _ _ hh), fun U => ?_⟩
  rw [D.limited X (fun i => ⟨o i,ho i⟩) R H P hh _ ?_]
  · apply congrArg Complex.exp; exact tsum_congr fun i => if_ctx_congr Iff.rfl (fun _ => (freeze X F P _ _).symm) fun _ => rfl
  intro i; by_cases h : Healthy P.threshold (X i) U
  · rw [masked_eq _ _ _ _ h]; exact (hF i).2 U h [] (Nat.zero_le _) (by simp)
  rw [masked_ne _ _ _ _ h,norm_zero]; exact (hF i).1
end Chorus

/-- Tape, chosen *without using the RG evaluation arrays*. Pack grouping may use
aggregates; no erasing the supports of the words. -/
noncomputable def logTape [Countable I] (X : I → Support n) (hn : ∀ i, (X i).Nonempty) : Chorus I n :=
  (peel X hn univ ∅ (empty_subset _)).choose

lemma tape_peeling [Countable I] (X : I → Support n) (hn : ∀ i, (X i).Nonempty) : Peeling X univ ∅ (logTape X hn) :=
  (peel X hn univ ∅ (empty_subset _)).choose_spec
end YM.Multi.Vacuum.Cluster
