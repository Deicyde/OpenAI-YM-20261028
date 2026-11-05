import Mathlib.Combinatorics.SimpleGraph.Acyclic
import YM.Extra.MULTISOURCE_BOUNDS.Rates
import YM.Further.DENSE_MIXED_KERNELS.View
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Work.A01.Mirror

/-!
# Buying the packet sizes in Forward

Unmarked expenses through the joint step are much harder than this
numeric conversion and remain explicit. Point estimates must use all retained
guards and tag costs (e.g. per compulsory packet), NOT a moment assuming
independence given Plot cuts. Here we integrate the verified packet tests
(`AbsoluteSums.Packets`) with the geometry prices of the mixed step.
E.g. buy the readable margin from the shared grants; provider supplies
Narrow with the tests on the actual remaining vertex weights. No E-derived
physics assumptions are silently available after roll choices. Takes D's
income BEFORE receiving a root estimate. Later use with specific Fee and
Gain committed in common C.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Filter Finset MeasureTheory Measure Lattice RG Wilson Precision Module Port Gaussian Surface
open Pressure Pressure.Stores
open Push.AbsoluteSums Push.AbsoluteSums.Packets
open Extra.Multi
open scoped NNReal ENNReal Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical

variable {G : Gauge} {A : ChartRatio G} {H : Port A} {m n : Side} {S : StepData m n} {Y : Type}

/-- Per-letter certificate *before* Hull and Kernel costs. Use ep as
precommitted per-seed reserve earmarked for paying forced kappa. -/
structure EmptyBook (S : StepData m n) (Y : Type) where
  pack : Y → Option (Stores S)
  rate : Y → ℝ
  ep : ℝ
  paid i : 0≤rate i
  pos : 0 ≤ ep

namespace EmptyBook
variable (E : EmptyBook S Y)

-- `depth`: path true length losses (if any) in vacuum quote must be
-- paid BEFORE this step. Geometry exposed here uses hull cover.
def depth (X : Y → Support m) (B : ℕ) (y : Y) :=
    max 1 ((E.pack y).elim (coverNumber B (X y)) (fun i => i.shares))
def down (y : Y) := (E.pack y).elim 1 (fun i => Real.exp (-E.ep*i.shares)) * E.rate y
lemma down_pos (y : Y) : 0 ≤ E.down y := by
  unfold down; cases E.pack y
  · exact mul_nonneg zero_le_one (E.paid y)
  exact mul_nonneg (Real.exp_pos _).le (E.paid y)
lemma down_le (y : Y) : E.down y ≤ E.rate y := by
  unfold down; cases E.pack y
  · exact mul_le_of_le_one_left (E.paid y) (le_refl 1)
  have ht := E.pos
  exact mul_le_of_le_one_left (E.paid y) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)))
lemma shield {y : Y} {i} (hi : E.pack y = some i) (hs : 0 < i.shares) {κ : ℝ} (hk : Real.exp (-E.ep) ≤ κ) :
    E.down y ≤ κ*E.rate y := by
  have hh : (1:ℝ) ≤ i.shares := by exact_mod_cast hs
  unfold down; rw [hi]; apply mul_le_mul_of_nonneg_right _ (E.paid _)
  have he := E.pos; apply le_trans _ hk; apply Real.exp_monotone; nlinarith

def optional (X : Y) := if E.pack X=none then E.rate X else 0

-- provider doesn't have to estimate the total connected component hit;
-- give thresholds *independent of volume* for realizing these individual
-- expenses. Accounts for variants, don't try to memoize spatial addresses
-- as though they were algebraic labels. Check against caller’s actual component inventory.
structure Narrow (X : Y → Support m) (l B : ℕ) (C gain spend eps ξ : ℝ) : Prop where
  step : ∀ i A,E.pack i=some A → X i ⊆ A.dome (l*B) ∧ Packets.connected S l B A
  packets A : Packets.connected S l B A → ∀ t : Finset Y, (∀ i∈t,E.pack i=some A) →
    ∑ i∈t,E.rate i ≤ Packets.income C spend gain A.shares
  rest : Ac.Hit X B E.optional (ξ+1) eps

def borrowed (j : ℕ) : ℝ := (Extra.Multi.exp_absorbs j 1 zero_lt_one).choose
lemma borrow_one (j) : 1 ≤ borrowed j := (Extra.Multi.exp_absorbs j 1 zero_lt_one).choose_spec.1
lemma absorb (j s : ℕ) : (1+(s:ℝ))^j ≤ borrowed j*Real.exp s := by
  simpa only [one_mul,borrowed] using (Extra.Multi.exp_absorbs j 1 zero_lt_one).choose_spec.2 s

def rocket (a : ℝ) (j B : ℕ) (X : Y→Support m) (y : Y) := a * (1+(E.depth X B y:ℝ))^j * E.rate y

variable {B l : ℕ} {ξ C q gain spend ε a : ℝ} {X : Y→Support m}
lemma renew (h : Narrow E X l B C gain spend ε ξ) (ha : 0 ≤ a) (j : ℕ) :
    Ac.Hit X B (fun i => if E.pack i=none then E.rocket a j B X i else 0) ξ (a*2^j*borrowed j*ε) := by
  intro x
  let D := a*2^j*borrowed j; have hd : 0 ≤ D := by unfold D; have he := borrow_one j; positivity
  refine Budget.mono (Budget.scale (h.rest x) hd) (fun i => ?_) (fun i => ?_) le_rfl
  · have hy : 0≤ E.rocket a j B X i := mul_nonneg (by positivity) (E.paid i)
    dsimp only; split_ifs <;> positivity
  dsimp only; split_ifs
  next hx hv =>
    unfold optional; rw [if_pos hv]; unfold rocket depth; rw [hv]; dsimp only [Option.elim_none]
    let s := coverNumber B (X i)
    have ht : 1+((max 1 s:ℕ):ℝ) ≤ 2*(1+s) := by
      rcases eq_zero_or_pos s with h|h; rw [h]; norm_num
      rw [max_eq_right h]; exact (by have := Nat.cast_nonneg (α:=ℝ) s; linarith)
    calc
      _ ≤ a*(2*(1+s))^j * E.rate i * Real.exp (ξ*s) := by
        have : 0≤ E.rate i := E.paid _
        gcongr
      _ ≤ a*(2^j*(borrowed j*Real.exp s)) * E.rate i * Real.exp (ξ*s) := by
        have : 0≤ E.rate i := E.paid _
        rw [mul_pow]; gcongr; exact absorb ..
      _ = D*(E.rate i * Real.exp ((ξ+1)*s)) := by
        unfold D; rw [add_mul,one_mul,Real.exp_add]; ring
  next _ h => simp [optional,h]
  rw [mul_zero]

-- reuse connected Packet grant counting on this actual op. Increases spend once
lemma exported (j : ℕ) (h : Narrow E X l B C gain spend ε ξ) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hf : fit S.patch.L l B ξ (spend+1) gain q) : Ac.Hit X B
    (fun i => if E.pack i=none then 0 else E.rocket a j B X i) ξ
      (Packets.totalCharge S.patch.L (a*borrowed j*C) l B q 0) := by
  let p (i) := (E.pack i).getD (Pressure.Stores.mk ∅ ∅ ∅)
  let d i := if E.pack i=none then 0 else E.rocket a j B X i
  have he i : 0≤d i := by
    unfold d rocket; split
    · rfl
    have hp := E.paid i; positivity
  have hp i (ht : d i ≠ 0) : E.pack i=some (p i) := by
    unfold p; generalize hu : E.pack i=q
    cases q
    · unfold d at ht; rw [if_pos hu] at ht; contradiction
    simp
  refine packet_variants S l B p X d (by have := borrow_one j; positivity) hf he (fun i hi =>
    (h.step _ _ (hp i hi)).symm) (fun A hA t ht => ?_)
  let H' := t.filter fun i=> d i ≠ 0
  have hm i (hm : i∈H') : E.pack i=some A := (hp i (mem_filter.mp hm).2).trans (congr_arg _ (ht i (mem_filter.mp hm).1))
  rw [← sum_subset (filter_subset _ _) (f:=d) (show ∀ i∈t,i∉H' → d i=0 from fun i hi hg => by_contra fun hb => hg (mem_filter.mpr ⟨hi,hb⟩))]
  calc
    _ = a * (1+(A.shares:ℝ))^j * (∑ i∈H', E.rate i) := by
      rw [mul_sum]; refine sum_congr rfl fun i hi => ?_
      unfold d rocket depth; simp [hm i hi, max_eq_right (Packets.shares_nonzero S l B hA)]
    _ ≤ a * (borrowed j*Real.exp A.shares) * Packets.income C spend gain A.shares := mul_le_mul
      (mul_le_mul_of_nonneg_left (absorb _ _) ha) (h.packets A hA H' hm) (sum_nonneg fun _ _=> E.paid _)
      (by have := borrow_one j; positivity)
    _ = _ := by
      unfold Packets.income; rw [show (spend+1-gain)*(A.shares:ℝ)= A.shares+(spend-gain)*(A.shares:ℝ) by ring, Real.exp_add]; ring

-- Numeric growth payment; doesn't posit convergence of component terms.
theorem lift (j : ℕ) (h : Narrow E X l B C gain spend ε ξ) (ha : 0 ≤ a)
    (hC : 0 ≤ C) (hf : fit S.patch.L l B ξ (spend+1) gain q) {eta : ℝ}
    (hh : a*2^j*borrowed j*ε + Packets.totalCharge S.patch.L (a*borrowed j*C) l B q 0 ≤ eta) :
      Ac.Hit X B (E.rocket a j B X) ξ eta := by
  intro x
  apply Push.AbsoluteSums.budget_loosen _ hh
  convert Budget.plus (E.renew h ha j x) (E.exported j h ha hC hf x) using 1; ext i; dsimp only; split_ifs <;> ring
end EmptyBook
end YM.Further.DenseMixedKernels
