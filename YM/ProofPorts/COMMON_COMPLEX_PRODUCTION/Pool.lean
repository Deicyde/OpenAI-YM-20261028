import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.LogAction
import YM.Next.FREE_KERNELS.Amend
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Covariance
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pin
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Story
import YM.Push.RELAY_DIFFERENCE.Shuffles


/-!
# Joint budgets on each conditional law

Pay consumption, exponential ratio coefficients and trigger nodes before
multiplying ANY estimates. Event index disjointness belongs to the counted
atoms (e.g., trigger nodes for distinct hot locations), not the original
backgrounds if those can require the SAME trigger. No statistical
independence assertion anywhere inside the connected term. Invocations
are all on the same true Z (including the exponential return from Pin and
the held-coordinate velocities). Cost of an exponential quadratic uses
the sum of weights, not the total volume, on the actual Z endpoints.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Function Filter Finset Matrix Lattice RG Wilson Precision Multi Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian Gauss Pressure Bid Tree YM.Push.SectorMeasure YM.Push.LogIdentity
open Component Arrival Desk Stamp
open scoped Topology BigOperators Classical MatrixOrder Tags

variable {I J : Type}

structure Pool (I J : Type) where
  sticker : I → ℝ -- instantaneous amplitude, before triggers and relative moments
  w : I → Vec J
  event : I → Finset J
  bill : I → ℝ -- min total real-square energy of event, incl EVERY derivative calling it

namespace Pool
variable (A : Pool I J) [Fintype J]

def meter (z : Vec J) (i : I) := A.sticker i * Real.exp (Gauss.pay (A.w i) z)

def occurring (s : Finset I) (z : Vec J) := ∀ i∈s, A.bill i ≤ ∑ j∈A.event i,z j ^2

def income (K : ℝ) (i : I) := A.sticker i * Real.exp (-Gauss.coin K*A.bill i + 2*K*((∑ j,A.w i j)+(A.event i).card * Gauss.coin K))

/-- Only local weight and covariance needed. bonus for any necessary
compulsory seed (e.g., output K). Last line pure product of allocated
price inequalities; no bound on the product of integrals or derivative
assembly assumed! `f` to include the charged incoming E/K multi options
with powers weighted by z.
-/
structure Funded (s : Finset I) (K bonus : ℝ) (f : I → ℝ) : Prop where
  price i : i∈s → 0 ≤ A.sticker i
  field i : i∈s → 0 ≤ A.w i
  distinct : (s : Set I).PairwiseDisjoint A.event
  ceiling j : K*(∑ i∈s,A.w i j) ≤ 1/8
  funds : (∏ i∈s,A.income K i) ≤ bonus * ∏ i∈s,f i

namespace Funded
variable {A} {s : Finset I} {K bonus : ℝ} {f : I→ℝ} (h : A.Funded s K bonus f)
include h
lemma positive (z : Vec J) (i : I) (hi : i∈s) : 0 ≤ A.meter z i := mul_nonneg (h.price i hi) (Real.exp_pos _).le

private lemma pays [DecidableEq J] : ∏ i∈s,A.income K i = (∏ i∈s,A.sticker i)*
    Real.exp (-coin K*(∑ i∈s,A.bill i) + 2*K*((∑ j,∑ i∈s,A.w i j) + (s.biUnion A.event).card * coin K)) := by
  rw [Finset.card_biUnion h.distinct]; push_cast
  unfold income; rw [Finset.prod_mul_distrib, ← Real.exp_sum]; congr 2
  rw [Finset.sum_add_distrib, sum_comm (s:=Finset.univ) (t:=s),sum_mul, mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib]

omit h in
private lemma furnished (z : Vec J) : ∏ i∈s,A.meter z i = (∏ i∈s,A.sticker i)*Real.exp (Gauss.pay (fun j => ∑ i∈s,A.w i j) z) := by
  unfold meter Gauss.pay; rw [Finset.prod_mul_distrib, ← Real.exp_sum]; congr 2; simp_rw [sum_mul]; rw [sum_comm]

/-- Integrated absolute price, usable even on a returned positive-order score or norm
used for pre-assembly series justification. Explicit costs for dimension/polynomial &
trigger debit (compare prodvv). -/
theorem joint [DecidableEq J] {Y M H : ℝ} {C : Gaussian.Table J} (hY : 0 ≤ Y) (hM : 0 ≤ M) (hK : 0≤K) (hH : 1≤H)
    (hc : 1+(Fintype.card J:ℝ) ≤ H*(1+Y)) (hC : C.PosDef) (ht : Ceiling C K)
    (k l : ℕ) (g : Vec J → ℂ) (hm : Measurable g)
    (hg : ∀ y : Vec J, g y≠0 → let z := CFC.sqrt C *ᵥ y
      ‖g y‖ ≤ M*(1+Y)^k * (1+squares z)^l * ∏ i∈s,A.meter z i ∧ A.occurring s z) :
    Integrable g (standard J) ∧ (∫ x, ‖g x‖ ∂standard J) ≤
      Gauss.coat K H l*M*(1+Y)^(l+k) * (bonus*∏ i∈s, f i) := by
  let b := ∑ i∈s,A.bill i; let w j := ∑ i∈s,A.w i j; let v := ∏ i∈s,A.sticker i
  have hv : 0≤v := prod_nonneg (s:=s) h.price
  let M' := M*(1+Y)^k; have hM' : 0≤M' := by unfold M'; positivity
  have hG : 0 ≤ Gauss.coat K H l := by unfold Gauss.coat; have := (coin_ok hK).1; have hH' := zero_le_one.trans hH; positivity
  have ht := gram_cost _ _ K (root_gram C hC) ht
  have hi := score (show Matrix J J ℝ from CFC.sqrt C) ht hK w (fun j => sum_nonneg fun i hi => h.field i hi _) h.ceiling l (s.biUnion A.event)
    (M'*v) b (∑ i,w i) g hm.aestronglyMeasurable (mul_nonneg hM' hv) le_rfl
    (Eventually.of_forall fun y hy => show _ from ?_)
  swap
  · obtain ⟨hh,ht⟩:=hg y hy
    rw [furnished] at hh
    exact ⟨hh.trans_eq (by unfold w v M'; change _ = M * (1+Y)^k * (∏ i∈s,A.sticker i) * (1+squares (CFC.sqrt C *ᵥ y))^l * Real.exp (Gauss.pay _ (CFC.sqrt C *ᵥ y)); ring), by rw [Finset.sum_biUnion h.distinct]; exact sum_le_sum ht⟩
  refine ⟨hi.1,(hi.2.trans (mul_le_mul_of_nonneg_left (Gauss.covered _ _ hK hH hY hc) (mul_nonneg hM' hv))).trans ?_⟩
  have hq := h.funds; rw [h.pays] at hq
  rw [pow_add]
  apply le_trans _ (mul_le_mul_of_nonneg_left hq (mul_nonneg (mul_nonneg hG hM) (by positivity)))
  unfold w v M' b; apply le_of_eq; ring
end Funded
end Pool
end YM.ProofPorts.CommonComplexProduction
