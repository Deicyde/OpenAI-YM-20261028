import YM.Push.CORRECTED_COLUMNS.Grows
import YM.Push.CORRECTED_COLUMNS.Links
import YM.Work.B13
/-!
# The purely numerical & positioning bills for restoration

Use `x=hatBeta_l`, `z=hatBeta_depth`, use accepted schedule and A
geometry; `Working` hypotheses can be met (see `feasible` *per fixed
numbers*, may include in price pages). Shrink and expand by actual powers
of p; expense of many atoms/counts paid on the indicated weights, using
shrinking hypotheses on the previous full K hit rate. Estimates show
required exponents possible. NO claim these estimates on rates themselves
(produce K with those rates etc.).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Corrected.Funding
open Function Set Filter Grows Lattice RG Cells MeasureTheory Wilson Marker Prepare Endpoint
open scoped Topology BigOperators Matrix.Norms.Frobenius

abbrev puff (z : ℝ) := Zone.Demand.cal z
-- Actual exponent arithmetic in comparison currencies
def checkp (x : ℝ) := Real.exp (y x ^ ((3:ℝ)/2))
def seed (x : ℝ) := (checkp x)^2

def crate (u : ℕ) := (u+u+1)^4
def times (B : ℕ) := (B+B+1)^4

structure Given where
  a : ℝ
  γ : ℝ
  U : ℝ
  C : ℝ
  c : ℝ
  u : ℕ
  D : ℝ
  δ : ℝ
  τ : ℝ
  ap : 0 ≤ a
  rp : 0 < γ
  Up : 0 ≤ U
  Cp : 0 < C
  cp : 0 < c
  dp : 0 < δ
  clash : δ+2*γ < τ

namespace Given
variable (S : Given)
abbrev box (x : ℝ) := (R x)^2
abbrev ε (S : Given) (k : ℝ) := (puff k)^(-S.τ)
abbrev output (S : Given) (k : ℝ) := (puff k)^S.γ
abbrev raw (S : Given) (k : ℝ) := (puff k)^(-S.U)
abbrev fee (S : Given) (k : ℝ) := Real.log (2+Real.exp S.D)+2*S.γ* Real.log (puff k)
abbrev T (S : Given) := Real.log (2+Real.exp S.D)+(S.a+1)*crate S.u
abbrev Λ (S : Given) := 2*(S.γ+S.U)+2*S.γ
abbrev limit (S : Given) (k : ℝ) := S.T+S.Λ*Real.log (puff k)
abbrev debit (S : Given) (x : ℝ) := S.C*Real.exp (-S.c*seed x)

structure Working (x z : ℝ) : Prop where
  weight : 1 ≤ S.output z
  coin : 0 < S.raw z
  take : S.raw z ≤ S.output z
  territory : box x ^2+2*(S.u*box x) ≤ R z^10
  space : 8 ≤ box x
  stays : (64:ℝ)*(Real.log (S.output z/S.raw z)*2) ≤ box x
  fit : 64*S.limit z ≤ box x
  rivals : Real.log (S.output z/S.raw z)*2+(S.a+1)*crate S.u+S.fee z ≤ S.limit z
  expFee : 1+S.output z^2*(Real.exp S.D+1) ≤ Real.exp (S.fee z)
  expBudget : 0 ≤ S.limit z
  bill : (times (box x):ℝ)*((1+(crate S.u*times (box x):ℕ))*Real.exp (S.limit z)*S.debit x) ≤ 1
  amount : (4:ℝ)*(S.output z^2*ε S z*Real.exp (S.a*crate S.u)) ≤ puff z^(-S.δ)
  restore : rewardK (S.limit z) (S.debit x) (crate S.u*times (box x)) ≤ Real.exp (-(S.c/3)*seed x)

omit S in
private lemma small (g f d : ℝ) (_hf : 0≤f) (hd : 0<d) : ∀ᶠ x : ℝ in atTop,
    g+f*Real.log (puff (2*x))≤ d*Real.log x := by
  have ht := (YM.Vac.Numbers.monitor f).comp (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hx : Tendsto (fun x => g/Real.log x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [hx.eventually (ge_mem_nhds (show 0<d/2 by positivity)),
    ht.eventually (ge_mem_nhds (show 0<d/4 by positivity)),eventually_gt_atTop (2:ℝ)] with x hx hh he
  have hp : 0 < Real.log x := Real.log_pos (by linarith)
  have hm : 0<Real.log (2*x) := Real.log_pos (by linarith)
  change f*Real.log (Real.log (2*x))^2 / Real.log (2*x) ≤ d/4 at hh
  rw [div_le_iff₀ hm] at hh
  have hg : g / Real.log x ≤ d/2 := hx
  rw [div_le_iff₀ hp] at hg
  unfold puff Zone.Demand.cal; rw [Real.log_exp]
  have ht : Real.log (2*x) ≤ 2*Real.log x := by
    rw [Real.log_mul (by positivity) (by linarith)]; have ht := Real.log_le_log (by positivity) he.le; linarith
  linarith only [hg, hh, mul_le_mul_of_nonneg_left ht hd.le]

omit S in
-- enough relative to seed (exp of (log-log)^(3/2))
private lemma suppressed (g f d : ℝ) (_hf : 0≤f) (hd : 0<d) : ∀ᶠ x : ℝ in atTop,
    g+f*Real.log (puff (2*x))≤ d*seed x := by
  filter_upwards [small g f d _hf hd,(Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 1,Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hx ht hu
  refine hx.trans (mul_le_mul_of_nonneg_left ?_ hd.le)
  have h : 1 < y x := ht
  have hp : y x ≤ y x^((3:ℝ)/2) := by
    conv_lhs => rw [← Real.rpow_one (y x)];
    exact Real.rpow_le_rpow_of_exponent_le h.le (by norm_num)
  have he : Real.log x ≤ checkp x := le_trans (Real.exp_log hu).symm.le (Real.exp_monotone hp)
  have ht : 1< checkp x := Real.one_lt_exp_iff.mpr (by positivity)
  apply he.trans
  unfold seed; nlinarith

-- Additional helper: curvature of prices


-- monotonic
omit S in
private lemma rises {x v : ℝ} (h₁ : 0<x) (h : x≤ v) (he : 1 ≤ Real.log x) : puff x ≤ puff v := by
  unfold puff Zone.Demand.cal; gcongr; exact Real.log_nonneg he


end Given

section buys
variable {G : Gauge} {C : Family G} {S : Table C.book} {d : ℕ} {X : Columns C S d} (Y : Tests X)
open Given Point RG.Supply Ac




-- At all sufficiently late k; no dependency choice on one chosen C yet.



open Given Endpoint
section
variable {q : Given} (N p k : ℕ)
variable (i : Row X) (c : AxisX X) (U : Wire C (Y.B.side k) (Y.B.depth k) N p)
variable {hp : Y.B.depth k≤N}
abbrev heads_addr (hp : Y.B.depth k≤N) (i : Row X) := Flow.origin Y k N p i hp ((Point.debits Y.B k).trans hp)
variable {K : Rep G (C.side (Point.middle Y.B k) p)} {T : Heads K.p (heads_addr Y N p k hp i) G} {F : Original K
    (heads_addr Y N p k hp i) (Marks.all (Endpoint.Copies Y k p × Mark X i))} {L : Atoms K.p (Marks.all (Endpoint.Copies Y k p × Mark X i)) (heads_addr Y N p k hp i) G ℕ}


end
end buys
end YM.Push.Corrected.Funding
