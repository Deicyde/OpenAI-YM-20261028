import YM.Planned.PRIMARY_INTEGRAL_295.Dunes
import YM.Planned.PRIMARY_INTEGRAL_295.Nimbuses
import YM.Planned.PRIMARY_INTEGRAL_295.Seas


/-!
# Gaussian-ring receipts at the component (single stratum)

Inputs lower-level than normalized Ops.Clock: E affine vector + linear
predictions at all strata, square roots from actual moving covariance in
physical marginal, Γ true independent-of-V cutoff on Z (NOT on x from
a standardization), payments as indicated. No assuming post-Gaussian
log estimates. Use with pointwise exact Raw phase not another kernel.

Costs including orders D via `Roof`. Noise parameter x shared everywhere
on a stratum. As in prior estimates all k incl 0.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Porous
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Source Source.Drops Wilson Oval Nimbuses Dunes
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E I : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]
variable {G : Gauge} {S : Finset Cover} {k : ℕ} {t s ξ M : ℝ}

/-- D includes b-copy piece (third) in absolute-log units / t.
Caller sends actual μ0 etc and must prove linear comparison `paid`;
use with true forest contacts and certified stationarity, NOT a claim
μ0 is the nonlinear critical branch. -/
structure Stand (I E : Type) [Fintype I] [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset Cover) (G : Gauge) where
  det : E → Dressed S G
  breeze : Sky I →L[ℝ] Dressed S G
  square : E → Sky I →L[ℝ] Sky I
  gamma : Sky I→ℝ

namespace Stand
variable (h : Stand I E S G)
-- normalized. insert β via ξ = g/t into W.

def bed (ξ : ℝ) (x : Sky I) (a : E) := h.det a + ξ • (h.breeze (h.square a x))
def skyW (B : Roof S G) (ξ t : ℝ) (x:Sky I) (a:E) := t⁻¹ • B.stitch (t • h.bed ξ x a)
def rho (x : Sky I) (a : E) : ℝ := h.gamma (h.square a x)

/-- One use with Clock radius R=1.

B._radius is pre-D&G.

M AFTER L used at true power. -/
structure Calls (B : Roof S G) (Q:E→Place.Dev S G) (t ξ s : ℝ) (k : ℕ) (M : ℝ) : Prop where
  paid : 1≤M
  size : (Fintype.card I:ℝ) ≤ M
  rate : t ∈ Ioc 0 1
  error : s∈Icc 0 1
  noise : ξ∈ Ioc 0 1
  charge : t*(2*M + M^2) ≤ B.radius
  serve : ContDiffAt ℝ k h.det 0 ∧ Oval.Envelope 0 k h.det M
  breathe : ‖h.breeze‖ ≤ M
  crown : ContDiffAt ℝ k h.square 0 ∧ Oval.Envelope 0 k h.square M
  -- Required to hold support on a fixed bounded gaussian norm on each
  -- finite-period computation. True non-degenerate no-hole.
  invert : ∃ N:ℝ, 0≤N ∧ ∀ x:Sky I, ‖x‖ ≤ N*‖h.square 0 x‖
  go : Fuzz 0 k (archL S G ∘ h.det) Q (M*s)
  profile : ContDiff ℝ k h.gamma ∧ ∀ z, Oval.Envelope z k h.gamma M
  cover : ∀ z, h.gamma z ∈ Icc 0 1 ∧
    (M * ξ * ‖z‖ ≤ 1 → h.gamma z=1) ∧ (M < ξ*‖z‖ → h.gamma z=0)

section
variable (B : Roof S G) {Q:E→Place.Dev S G} (hc : h.Calls B Q t ξ s k M)

include hc

lemma sphere (x : Sky I) : ContDiffAt ℝ k (fun y=>h.square y x) 0 ∧
    Oval.Envelope 0 k (fun y=>h.square y x) (M*‖x‖) := by
  have hm:=hc.paid
  refine ⟨hc.crown.1.clm_apply contDiffAt_const,by positivity,fun n hn=> ?_⟩
  rw [mul_comm M]; exact (norm_iteratedFDeriv_clm_apply_const hc.crown.1 (Nat.cast_le.mpr hn)).trans
    (mul_le_mul_of_nonneg_left (hc.crown.2.2 n hn) (norm_nonneg _))
lemma passing (x : Sky I) : ContDiffAt ℝ k (fun a:E=>ξ • (h.breeze (h.square a x))) 0 ∧
    Oval.Envelope 0 k (fun a:E=>ξ • (h.breeze (h.square a x))) (M^2*ξ*‖x‖) := by
  let q (a:E) := h.square a x
  obtain ⟨hf,hz⟩:= h.sphere B hc x
  have hg : ContDiffAt ℝ k (h.breeze ∘ q) 0 := h.breeze.contDiff.contDiffAt.comp _ hf
  refine ⟨hg.const_smul _,?_⟩
  have he := Seas.scaleBy hg ξ _ (Seas.paidLinear h.breeze hf hz hc.breathe)
  rw [Real.norm_of_nonneg hc.noise.1.le,show ξ*(M*(M*‖x‖))=M^2*ξ*‖x‖ by ring] at he; exact he
lemma bed_cost (x : Sky I) : ContDiffAt ℝ k (h.bed ξ x) 0 ∧ Oval.Envelope 0 k (h.bed ξ x) (2*M^2 * breath x) := by
  obtain ⟨hc',hp⟩:= h.passing B hc x
  have hm:=hc.paid
  refine ⟨hc.serve.1.add hc',Seas.less (Seas.add hc.serve.1 hc' hc.serve.2 hp) ?_⟩
  unfold breath; have ht:=hc.noise.2
  have hz:= show M≤M^2 by nlinarith
  have hh:=mul_le_mul_of_nonneg_right (show M^2*ξ≤M^2 from mul_le_of_le_one_right (by positivity) ht) (norm_nonneg x)
  linarith [show 0 ≤ M^2*‖x‖ by positivity]

lemma W_clean (x : Sky I) : ContDiffAt ℝ k (h.skyW B ξ t x) 0 := by
  have hh := (h.bed_cost B hc x).1
  have he := (B.smooth.of_le (m:=(k:WithTop ℕ∞)) (by exact_mod_cast le_top)).contDiffAt.comp (f:=fun a => t • h.bed ξ x a) (0:E) (hh.const_smul t)
  exact he.const_smul t⁻¹
lemma exposed (x : Sky I) : ContDiffAt ℝ k (h.rho x) 0 ∧ Oval.Envelope 0 k (h.rho x)
    (k.factorial*M*(1+M)^k*breath x^k) := by
  obtain ⟨ht,he⟩:=h.sphere B hc x; have hm:=hc.paid
  refine ⟨hc.profile.1.contDiffAt.comp _ ht, Seas.less (Seas.joined hc.profile.1 ht he (hc.profile.2 _)) ?_⟩
  rw [mul_assoc (_*M),← mul_pow];
  apply mul_le_mul_of_nonneg_left _ (by positivity); refine pow_le_pow_left₀ (by positivity) ?_ _; unfold breath; linarith [norm_nonneg x]

lemma tent_whenever : ∀ᶠ a:E in 𝓝 0, ∀ (x:Sky I), ξ*‖h.square a x‖≤M → ‖t • h.bed ξ x a‖ ≤ B.radius := by
  have hp:= hc.serve.2.value; have hm := hc.paid
  have ht:=hc.noise.1; have hq:=hc.rate.1
  filter_upwards [hc.serve.1.continuousAt.norm.eventually (ge_mem_nhds (show ‖h.det 0‖<2*M by linarith))] with a ha x hx
  rw [norm_smul,Real.norm_of_nonneg hq.le];
  apply (mul_le_mul_of_nonneg_left _ hq.le).trans hc.charge
  apply (norm_add_le ..).trans (add_le_add ha _); rw [norm_smul,Real.norm_of_nonneg ht.le]
  have he := (h.breeze.le_opNorm (h.square a x)).trans (mul_le_mul_of_nonneg_right hc.breathe (norm_nonneg _))
  calc
    _ ≤ ξ*(M*‖h.square a x‖) := mul_le_mul_of_nonneg_left he ht.le
    _ = M*(ξ*‖h.square a x‖) := mul_left_comm ..
    _ ≤ _ := (mul_le_mul_of_nonneg_left hx (zero_le_one.trans hm)).trans_eq (pow_two M).symm

lemma within (x : Sky I) (ht : Purse.Present (h.rho x) 0 k) : ξ*‖h.square 0 x‖ ≤ M := by
  by_contra! hz
  apply ht
  have hc' : h.rho x =ᶠ[𝓝 (0:E)] 0 := by
    have hh:=show ContinuousAt (fun y=>ξ*‖h.square y x‖) 0 from
      continuousAt_const.mul (h.sphere B hc x).1.continuousAt.norm
    exact (hh.eventually (lt_mem_nhds hz)).mono fun y hy=> (hc.cover _).2.2 hy
  refine ⟨hc'.self_of_nhds, Finset.sum_eq_zero fun i _=>?_⟩
  rw [(hc'.iteratedFDeriv ℝ _).self_of_nhds]; simp
end
end Stand

-- Seal price from Seas across Gaussian θ; tag dimensionality or L not used.
def rootPrice (B : Roof S G) (k:ℕ) := (Seas.expenseLog.{0,0,0} (archL S G) B.stitch B.smooth B.launch B.rule k B.radius).choose

end YM.Planned.PrimaryIntegral295.Porous
