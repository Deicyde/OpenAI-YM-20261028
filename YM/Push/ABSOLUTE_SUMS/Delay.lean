import YM.Push.ABSOLUTE_SUMS.Charge
import YM.Work.E09.Scales


/-!
# Fixed-L delay: tree-vertex prices from the grant scale

Numerical lemma, separate from testing the grant on actual data and from
**obtaining** clocks that carry these delays. Works for the actual comparison
`x = βhat_c`, `betaF = βhat_f`. No upper bound on the actual β needed for
the combinatorial implication (where there are β-dependent costs the
hypothesis on their sizes still applies). Delay can depend on L and on all
the indicated parameters. It CANNOT depend on the volume and doesn't.
This is not a scheduling claim (see RPre etc).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.AbsoluteSums.Delay
open Filter YM.Pressure Lattice Animals Packets
open scoped Topology BigOperators

variable (G : Gauge) (L : Side)

def fineMonitor (x : ℝ) := Vac.Numbers.P (betaF G x L)
-- convenient polynomial expense scale for B, log of coupling, etc.
def bill (x : ℝ) : ℝ := 1 + (radiusB x:ℝ) + Real.log (betaF G x L)^2
-- u: ratio floor on beta, e.g. 1/2; mu: earned grant rate (or a reserved fraction).
def hatWin (μ u x : ℝ) := μ*u*fineMonitor G L x^2

def retained (μ u x : ℝ) := Real.exp (-hatWin G L μ u x/2)

lemma monitor_pos (x : ℝ) : 0 < fineMonitor G L x := Real.exp_pos _
lemma bill_ge (x : ℝ) : 1 ≤ bill G L x := by
  dsimp only [bill]; have he := Nat.cast_nonneg (α := ℝ) (radiusB x)
  linarith [sq_nonneg (Real.log (betaF G x L))]

lemma win_pos {μ u : ℝ} (x : ℝ) (hm : 0 < μ) (hu : 0 < u) : 0 < hatWin G L μ u x := by
  unfold hatWin; have h := monitor_pos G L x; positivity

lemma shift_pos : ∀ᶠ x : ℝ in atTop, 0 < betaF G x L :=
    (Work.E09.betaF_growth G L).eventually (eventually_gt_atTop 0)

lemma comparison {x μ u : ℝ} (hx : 0 < betaF G x L) (hm : 0 < μ) (β : ℝ)
    (hβ : u*betaF G x L ≤ β) : hatWin G L μ u x ≤ β*(μ*(fiery G x L)^2) := by
  have hy : betaF G x L * (fiery G x L)^2 = fineMonitor G L x ^ 2 := by
    have h := Real.sqrt_pos.mpr hx
    unfold fiery temp fineMonitor Vac.Numbers.P
    field_simp
    rw [Real.sq_sqrt hx.le]
  calc
    _ = (u*betaF G x L)*(μ*(fiery G x L)^2) := by unfold hatWin; rw [← hy]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hβ (by positivity)

private lemma small_bill : ∀ᶠ x : ℝ in atTop, bill G L x ≤ 7 * Real.log (betaF G x L)^2 := by
  let k := G.slopeConstant*Real.log L.val
  have he := Work.E09.betaF_growth G L
  filter_upwards [eventually_gt_atTop (4:ℝ),eventually_gt_atTop (-2*k),he.eventually (eventually_gt_atTop 1),
    (Real.tendsto_log_atTop.comp he).eventually (eventually_ge_atTop 1)] with x hx hy h hv
  let s := betaF G x L
  have hk : x/2 ≤ s := by change x/2 ≤ x+k; linarith
  have h1 : 0 < s := by change 1 < s at h; linarith
  have h2 : x ≤ s^2 := by nlinarith
  have h3 : 1 ≤ Real.log s := hv
  have h4 : Real.log x ≤ 2 * Real.log s := calc
    _ ≤ Real.log (s^2) := Real.log_le_log (by linarith) h2
    _ = _ := by rw [Real.log_pow]; norm_num
  have hh : (radiusB x:ℝ) < (Real.log x)^2+1 := Nat.ceil_lt_add_one (sq_nonneg _)
  change 1+(radiusB x:ℝ)+Real.log s ^ 2 ≤ _
  change 1+(radiusB x:ℝ)+Real.log s ^ 2 ≤ 7 * Real.log s ^ 2
  nlinarith [Real.log_pos (show 1<x by linarith)]

/-- Positive powers of the monitor (NOT only of beta) dominate every
fixed power of the bill. -/
lemma monitor_pays (d : ℕ) {D e : ℝ} (hD : 0 ≤ D) (he : 0 < e) :
    ∀ᶠ x : ℝ in atTop, D * bill G L x^d ≤ fineMonitor G L x ^ e := by
  let C := D * (7:ℝ)^d
  have hC : 0 ≤ C := by unfold C; positivity
  have hv := Real.tendsto_log_atTop.comp (Work.E09.betaF_growth G L)
  filter_upwards [small_bill G L,hv.eventually (eventually_gt_atTop 0),
    (Real.tendsto_log_atTop.comp hv).eventually (eventually_gt_atTop 1),
    (Real.tendsto_log_atTop.comp hv).eventually (eventually_ge_atTop ((C+2*d)/e))] with x h1 h2 h3 h4
  let v := Real.log (betaF G x L)
  let w := Real.log v
  have hx : 0 < v := h2
  have ht : 1 ≤ w := by change 1 < w at h3; linarith
  have hb : (C+2*d)/e ≤ w := h4
  calc
    _ ≤ D*(7*v^2)^d := mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (zero_le_one.trans (bill_ge G L x)) h1 d) hD
    _ = C * Real.exp ((2*d)*w) := by
      have hj : v = Real.exp w := (Real.exp_log hx).symm
      unfold C; rw [mul_pow,mul_assoc]; congr 1
      rw [hj,← Real.exp_nat_mul,← Real.exp_nat_mul]; congr 1; push_cast; ring_nf
    _ ≤ Real.exp C * Real.exp ((2*d)*w) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp C]
    _ ≤ Real.exp (w^2*e) := by
      rw [← Real.exp_add,Real.exp_le_exp]
      have hy := (div_le_iff₀ he).mp hb
      nlinarith [mul_le_mul_of_nonneg_right hy (show 0 ≤ w by linarith)]
    _ = _ := Real.exp_mul _ _

lemma wins {μ u z D : ℝ} (hm : 0 < μ) (hu : 0 < u) (hD : 0 ≤ D) (hz : z < 2) (d : ℕ) :
    ∀ᶠ x : ℝ in atTop, D * bill G L x^d * fineMonitor G L x^z ≤ hatWin G L μ u x / 16 := by
  have he : 0 ≤ 16*D/(μ*u) := by positivity
  filter_upwards [monitor_pays G L d he (sub_pos.mpr hz)] with x hx
  let P := fineMonitor G L x
  have hp : 0 < P := monitor_pos G L x
  change _ ≤ P ^ (2-z) at hx
  rw [Real.rpow_sub hp] at hx
  have hg : (P^(2:ℝ)) = P^(2:ℕ) := Real.rpow_two _
  have hh : 0 < P^z := Real.rpow_pos_of_pos hp z
  rw [hg] at hx
  have h := (le_div_iff₀ hh).mp hx
  unfold hatWin; change _ * P^z ≤ μ*u*P^(2:ℕ)/16
  have hs : 0<μ*u := by positivity
  field_simp at h
  linarith

lemma bill_pays {μ u D : ℝ} (hm : 0 < μ) (hu : 0 < u) (hD : 0 ≤ D) (d : ℕ) :
    ∀ᶠ x : ℝ in atTop, D * bill G L x^d ≤ hatWin G L μ u x/16 := by
  simpa only [Real.rpow_zero,mul_one] using wins G L hm hu hD (by norm_num : (0:ℝ)<2) d

section Entropy

private def degreeConst (L : Side) (l : ℕ) := (typesAt L:ℝ) * ((4*l+5:ℕ):ℝ)^4

lemma step_delay (l : ℕ) {μ u : ℝ} (hm : 0 < μ) (hu : 0 < u) :
    ∀ᶠ x : ℝ in atTop,
      let z := Real.exp (hatWin G L μ u x/16)
      ((hitCost L l (radiusB x):ℕ):ℝ) ≤ z ∧
        ((stepCost L l (radiusB x)^2:ℕ):ℝ) ≤ z := by
  have hd : 0 ≤ degreeConst L l := by unfold degreeConst; positivity
  filter_upwards [bill_pays G L hm hu (sq_nonneg (degreeConst L l)) 8] with x hx
  let B := radiusB x; let E := bill G L x; let m := hatWin G L μ u x
  let z := Real.exp (m/16)
  have h1 : 0 ≤ ((stepCost L l B : ℕ):ℝ) := Nat.cast_nonneg _
  have h2 : ((stepCost L l B : ℕ):ℝ) ≤ degreeConst L l * E^4 := by
    have hb : (B:ℝ) ≤ E := by
      dsimp only [B,E,bill]; linarith [sq_nonneg (Real.log (betaF G x L))]
    have he : 1 ≤ E := bill_ge G L x
    unfold degreeConst stepCost ballCost
    push_cast; rw [mul_comm _ (typesAt L:ℝ),mul_assoc,← mul_pow]
    -- order monotonicity incl Nat casts
    gcongr
    nlinarith
  have h3 : m/16 ≤ z := by unfold z; linarith [Real.add_one_le_exp (m/16)]
  have h4 : ((stepCost L l B ^ 2:ℕ):ℝ) ≤ z := calc
    _ ≤ (degreeConst L l * E^4)^2 := by rw [Nat.cast_pow]; gcongr
    _ = degreeConst L l ^2*E^8 := by ring
    _ ≤ _ := hx.trans h3
  refine ⟨le_trans ?_ h4,h4⟩
  have he : hitCost L l B ≤ stepCost L l B := by
    unfold hitCost stepCost ballCost; gcongr <;> omega
  have ht := step_ge L l B
  exact_mod_cast (show hitCost L l B ≤ stepCost L l B^2 by nlinarith)
end Entropy

/-- Delay suffices for all the PER-PACKET combinatorial tests here.
Bills allowed to multiply even a fixed power of fine monitor < 2 in
log-price. Constants precommitted (arbitrary fixed L here); spend,
C and gain may vary on the actual band. `q` and all ceilings independent
of c, f, root and addresses. Reserve reduction gives a particularly useful
`exp(-Θ(hatWin)*m)` bound. -/
lemma fits (l : ℕ) {μ u a D z : ℝ} (hm : 0 < μ) (hu : 0 < u) (ha : 0 ≤ a) (hD : 0 ≤ D)
    (d : ℕ) (hz : z < 2) :
    ∀ᶠ x : ℝ in atTop, ∀ (spend gain C : ℝ),
      let B := radiusB x; let M := hatWin G L μ u x; let q := retained G L μ u x
      let cost := D * bill G L x^d * fineMonitor G L x^z
      spend ≤ cost → M ≤ gain → 0 ≤ C → C ≤ Real.exp cost →
      fit L l B a spend gain q ∧ ∀ m : ℕ, totalCharge L C l B q m ≤ Real.exp (-M/4*(max 1 m:ℕ)) := by
  have hA : 0 ≤ a*(seedCover l:ℝ) := by positivity
  filter_upwards [wins G L hm hu hD hz d,bill_pays G L hm hu (show 0 ≤ (2:ℝ) by norm_num) 0,
    bill_pays G L hm hu hA 0,step_delay G L l hm hu] with x hx h2 ha' hs spend gain C
  intro B M q cost hw hg hC hb
  rw [pow_zero,mul_one] at ha' h2
  let p := Real.exp (M/16)
  have hcost : cost ≤ M/16 := hx
  have hcc : C ≤ p := hb.trans (Real.exp_monotone hcost)
  obtain ⟨hl,hS⟩ := hs
  have hy : 2 ≤ M/16 := h2
  have hp : 2 ≤ p := by unfold p; linarith [Real.add_one_le_exp (M/16)]
  have hq : q ≤ 2⁻¹ := by
    change Real.exp (- _ /2) ≤ _
    rw [neg_div,Real.exp_neg]
    have hn : p ≤ Real.exp (M/2) := Real.exp_monotone (by linarith)
    exact inv_anti₀ (by norm_num) (hp.trans hn)
  constructor
  · refine ⟨ha,?_,by linarith⟩
    unfold ratioCost oneCost
    apply (mul_le_mul_of_nonneg_right hS (Real.exp_pos _).le).trans
    change p * Real.exp _ ≤ Real.exp (-M/2)
    unfold p; rw [← Real.exp_add]
    apply Real.exp_monotone; change a*seedCover l ≤ M/16 at ha'
    linarith
  intro m
  let n := max 1 m
  have hj : 0 ≤ q := (Real.exp_pos _).le
  have hi : (1-q)⁻¹ ≤ p := calc
    _ ≤ ((2:ℝ)⁻¹)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ ≤ _ := by rwa [inv_inv]
  unfold totalCharge
  calc
    _ ≤ (p*p)*q^n*p := by
      have he : 0 < 1-q := by linarith
      gcongr
    _ = Real.exp (M/16+M/16+(n:ℝ)*(-M/2)+M/16) := by
      change p*p*Real.exp _^n*p = _
      simp only [← Real.exp_nat_mul,Real.exp_add,p,M]
    _ ≤ _ := by
      apply Real.exp_monotone
      change _ ≤ -M/4*(n:ℝ)
      have he : 1 ≤ (n:ℝ) := by exact_mod_cast (le_max_left 1 m)
      nlinarith

/-- Useful for small-hit thresholds expressed with fixed polynomial
losses. -/
lemma sawn {μ u A D z : ℝ} (hm : 0 < μ) (hu : 0 < u) (hA : 0 < A)
    (hD : 0 ≤ D) (d : ℕ) (hz : z < 2) :
    ∀ᶠ x : ℝ in atTop,
      let M := hatWin G L μ u x
      D * bill G L x^d * fineMonitor G L x^z * Real.exp (-M/4) ≤ A := by
  filter_upwards [wins G L hm hu (div_nonneg hD hA.le) hz d] with x h
  intro M
  let e := D * bill G L x^d * fineMonitor G L x^z
  change (D/A)*_ * _ ≤ M/16 at h
  have he : e/A ≤ M/16 := by unfold e; rw [show D*_ *_/A=D/A*(bill G L x^d)*(fineMonitor G L x^z) by ring]; exact h
  rw [neg_div,Real.exp_neg,← div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)]
  have hi : 0 < M := win_pos G L x hm hu
  have hr : M/16 ≤ Real.exp (M/4) := by linarith [Real.add_one_le_exp (M/4)]
  exact ((div_le_iff₀ hA).mp (he.trans hr)).trans_eq (mul_comm ..)
end YM.Push.AbsoluteSums.Delay
