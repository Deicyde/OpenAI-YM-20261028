import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Moments
import YM.Push.CUTOFF_PROJECTORS.Equations


/-!
# Budget a local test, at its given index and fixed order

Compulsory residual energy is combined (not using separate unsigned
upper prices on the many rows!). The specified spare aperture pays only
ratio / other endpoint exponential factors. It must be charged for EVERY
selected occurrence using that point, and triggers can be credited once
from the unspent part. All tests refer to one Gaussian and its actual Z
(the comparison version retests at each reference).
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice Wilson RG Next.SectorChange Next.SectorChange.Gaussian Moments
open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators RealInnerProductSpace

/-- Constants at this local billing call. Uniformity comes from BUYING
these numbers with the required dependencies before use. They do NOT
vary throughout a point calculation (in z), except for the formulas here
like `quota` and `grow`. See `Office` exercise to see some of the
buys that can be guaranteed so far. α unlogged, β logs being kept
(core subset must be genuinely tested residual rows), γ remaining log
complements. Mismatched comparison or other use not presumed to keep
this ticket. -/
structure Tariff (α β γ ι : Type) where
  core : Finset β
  /-- exponent income from selected affine-subtracted action rows. Negative
  is gain (e.g. suppression in a compulsory packet). -/
  value : ℝ
  /-- exponent currencies for other kept quantities (e.g., deficits for
  frozen charts, local determinant entries). -/
  cost : β → ℝ
  port : α → ℝ
  wage : γ → ℝ
  /-- Log entry tolerance (including its derivatives at the stated rate) -/
  quota : γ → Vec ι → ℝ
  /-- Per-coordinate quadratic growth charges; includes adjusting from
  input `quota` to square-root envelopes for the resulting Mayer factors. -/
  send : α → ι → ℝ
  wait : β → ι → ℝ
  use : γ → ι → ℝ
  seat : Finset ι
  capacity : ℝ
  mark : ι → ℝ
  stake : ℝ
  ray : ℝ
  orderPay : ℕ

namespace Tariff
variable {α β γ ι : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι] [DecidableEq β]
    (b : Tariff α β γ ι)

def reach (j : ι → ℝ) (z : Vec ι) := ∑ i∈b.seat, j i * z i ^ 2

def grow (z : Vec ι) := b.ray * powers z ^ b.orderPay

/-- α gate prices (including any masks, unit-inventory predicates etc.) -/
def portal (i : α) (z : Vec ι) := b.port i * Real.exp (b.reach (b.send i) z)
/-- Untouched exponential caps (besides the *aggregate* `core`). -/
def invoice (i : β) (z : Vec ι) := b.cost i + b.reach (b.wait i) z
/-- optional exp(q)-1 envelopes. Does not determine q's sign. -/
def slide (i : γ) (z : Vec ι) := b.wage i * Real.exp (b.reach (b.use i) z)

/-- Revenue beyond the row energy, from requiring a large Z. Use
only with the *joint* lease at these exact parameters. -/
def Event (z : Vec ι) := b.stake ≤ b.reach b.mark z

/-- This is the load test on ALL factors. Merely purchasing each under its
parent's own marginal doesn't entitle use in this product. (Where one
factor depends on another's applicability, see the Clearance consumer too.)
We choose explicit but not tight powers (e.g., might take very large ray for
a fixed few derivative prices). -/
structure Lease : Prop where
  size : 0 < b.capacity
  landed : ∀ i ∈ b.seat, b.mark i + (∑ j : α,b.send j i) + (∑ j∈b.coreᶜ,b.wait j i) +
    (∑ j : γ,b.use j i) ≤ b.capacity⁻¹/8
  high : 1 ≤ b.ray
  present i : 0 ≤ b.port i
  wages i : 0 ≤ b.wage i
  earmark i z : Real.exp (b.quota i z)*b.quota i z ≤ b.slide i z
  born i z : b.quota i z ≤ b.grow z

/-- Result weight before moments. -/
def salary := (∏ i,b.port i)*(∏ i,b.wage i)*Real.exp (b.value + (∑ i∈b.coreᶜ,b.cost i)-b.stake)

def codex (z : Vec ι) := b.salary * Real.exp (b.capacity⁻¹/8*load b.seat z)

namespace Lease
variable {b}
lemma pays_grow (h : b.Lease) (z : Vec ι) : 1 ≤ b.grow z := one_le_mul_of_one_le_of_one_le h.high (one_le_pow₀ (grows z))

lemma solvent (h : b.Lease) : 0 ≤ b.salary := by
  unfold salary; exact mul_nonneg (mul_nonneg (Finset.prod_nonneg (fun i _ => h.present i)) (Finset.prod_nonneg (fun i _ => h.wages i))) (Real.exp_pos _).le

lemma fair (h : b.Lease) (z : Vec ι) : 0 ≤ b.codex z := mul_nonneg h.solvent (Real.exp_pos _).le

lemma paid (h : b.Lease) (z : Vec ι) (hh : b.Event z) :
    (∏ i,b.portal i z)*Real.exp (b.value + ∑ i∈b.coreᶜ,b.invoice i z) * (∏ i,b.slide i z) ≤ b.codex z := by
  let P := ∏ i,b.port i; let W := ∏ i,b.wage i
  let S := ∑ i,b.reach (b.send i) z
  let U := ∑ i,b.reach (b.use i) z
  let V := ∑ i∈b.coreᶜ,b.reach (b.wait i) z
  let Y := b.value + ∑ i∈b.coreᶜ,b.cost i
  have he : b.reach b.mark z + S + V + U ≤ b.capacity⁻¹/8*load b.seat z := calc
    _ = ∑ i∈b.seat,(b.mark i + (∑ j,b.send j i) + (∑ j∈b.coreᶜ,b.wait j i) + (∑ j,b.use j i))*z i ^ 2 := by
      unfold S U V reach; simp_rw [add_mul,Finset.sum_mul,Finset.sum_add_distrib]
      congr 1
      · congr 1
        · congr 1; exact Finset.sum_comm
        · exact Finset.sum_comm
      exact Finset.sum_comm
    _ ≤ ∑ i∈b.seat, b.capacity⁻¹/8*z i ^ 2 := Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (h.landed i hi) (sq_nonneg _)
    _ = _ := Finset.mul_sum .. |>.symm
  unfold portal slide; simp only [Finset.prod_mul_distrib, ← Real.exp_sum]
  rw [show (b.value + ∑ i∈b.coreᶜ,b.invoice i z)=Y+V by unfold invoice Y V; rw [Finset.sum_add_distrib, add_assoc]]
  change (P*Real.exp S)*Real.exp (Y+V)*(W*Real.exp U) ≤ P*W*Real.exp (Y-b.stake)*_
  rw [show (P*Real.exp S)*Real.exp (Y+V)*(W*Real.exp U)=P*W*Real.exp (S+(Y+V)+U) by rw [Real.exp_add (S+(Y+V)) U,Real.exp_add S]; ring,
    mul_assoc (P*W),← Real.exp_add]
  exact mul_le_mul_of_nonneg_left (Real.exp_monotone (by unfold Event at hh; linarith only [he,hh])) (mul_nonneg
    (Finset.prod_nonneg (fun i _ => h.present i)) (Finset.prod_nonneg (fun i _ => h.wages i)))
end Lease

section construction
-- Numerical (E:eq:Eenv). Repetitions at endpoints go in the λ-test with
-- their actual multiplicity; can equally use disjoint site blocks.
omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [Fintype ι] in
lemma prepaid (x : ℝ) (hx : 0 ≤ x) (s : Finset ι) (hs : s ⊆ b.seat) (z : Vec ι) [DecidableEq ι] :
    let q := x^2*(1+load s z)
    Real.exp q*q ≤ (x*Real.exp (x+x^2))* Real.exp (b.reach (fun i => if i∈s then x+x^2 else 0) z) := by
  let t := 1+load s z; let v := x+x^2
  have ht : 0 ≤ t := add_nonneg (by norm_num) (load_nonneg ..)
  intro q
  have he : b.reach (fun i => if i∈s then v else 0) z=v*load s z := by
    unfold Tariff.reach load; rw [Finset.mul_sum, ← Finset.sum_subset hs (f:=fun i => (if i∈s then v else 0)*z i^2) (fun i _ hi => by simp [hi])]
    exact Finset.sum_congr rfl fun i hi => by rw [if_pos hi]
  have hh : x*t ≤ Real.exp (x*t) := by linarith only [Real.add_one_le_exp (x*t)]
  rw [he]; change _ ≤ (x*Real.exp v)*Real.exp (v*load s z)
  calc
    Real.exp q*q=Real.exp q*x*(x*t) := by unfold q t; ring
    _ ≤ Real.exp q*x*Real.exp (x*t) := by gcongr
    _ = _ := by rw [mul_comm (Real.exp q) x,mul_assoc x,mul_assoc x,← Real.exp_add,← Real.exp_add]; unfold q v t; ring_nf
end construction
end Tariff
end YM.AnalyticBridge.LocalGaussian
