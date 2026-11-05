import YM.Pert.Parity.End
/-!
Extract the leading log of **the same** running inverse action coefficient (including the finite-cutoff bare coupling endpoint), using the actual `Family.Makes` running control, not merely the reference linear term of hatBeta.
No statement that this proxy equals the physical X-scheme coupling beyond the extracted comparison; in particular its numeric existence does not implement the tangent-one `bUU` test.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Pert.Asymptotics
open Filter Function Topology Spec RG
open scoped Topology
variable {G : Gauge} {I : Extraction.Order} {C : Family G} {S : Table C.book}

def b0 (G : Gauge) := 11*G.casimir / (48*Real.pi^2)
theorem b0_normalizes : 2*b0 G = G.slopeConstant := by rw [b0,Gauge.slopeConstant]; ring
lemma zeroUp_bound (C : Family G) (hc : C.Makes) {ε : ℝ} (he : 0<ε) : ∀ᶠ m in atTop,
    ∀ N p : ℕ, m≤N → |C.path.β N p m / C.S.scale m - 2*b0 G| < ε := by
  have hh := hc.wilson.running (ε/4) (by positivity)
  let a := C.path.levels.clock.bar
  filter_upwards [hh,C.S.divergent.eventually_ge_atTop ((|a|+1)/(ε/4))] with m hm hv N p hn
  rw [div_le_iff₀ (by positivity)] at hv
  have hk := hm N p hn
  change |C.path.β N p m-(a + G.slopeConstant * C.S.scale m)|≤_ at hk
  rw [← b0_normalizes] at hk
  let r := C.S.scale m
  have hr : 0<r := by nlinarith [abs_nonneg a]
  let β:= C.path.β N p m
  have ha := abs_add_le (β-(a+2*b0 G*r)) a
  have h₁ : |β-2*b0 G*r|<ε*r := by rw [show β - (a + 2 * b0 G * r) + a = β - 2 * b0 G * r by ring] at ha; exact ha.trans_lt (by dsimp [β,r]; nlinarith)
  rw [show β/r-2*b0 G=(β-2*b0 G*r)/r from by field_simp [hr.ne'],abs_div,abs_of_pos hr] -- maybe no goal
  exact (div_lt_iff₀ hr).2 h₁

variable {N k : ℕ→ ℕ} (hc : C.Makes) (hg : G.Simple)
include hc hg

def regulatorRun (C : Family G) (N p m) := (Real.sqrt (C.path.β N p m))⁻¹
theorem comparison (hi : ∀ᶠ i : ℕ in atTop, i≤N i) : Tendsto (fun i => regulatorRun C (N i) (k i) i * Real.sqrt (Real.log ((C.S.a i)⁻¹))) atTop (𝓝 ((Real.sqrt (2*b0 G))⁻¹)) := by
  let a := fun i=>C.path.β (N i) (k i) i
  have hp := C.S.divergent.eventually_gt_atTop 0
  have hl : Tendsto (fun i=>a i/C.S.scale i) atTop (𝓝 (2*b0 G)) := Metric.tendsto_nhds.2 (fun ε h => by
      filter_upwards [zeroUp_bound C hc h,hi] with i hr hm; rw [Real.dist_eq]; exact hr _ _ hm)
  have hf := (Real.continuous_sqrt.continuousAt (x:=2*b0 G)).tendsto.comp hl
  have hx := hf.inv₀ (show Real.sqrt (2*b0 G)≠0 from Real.sqrt_ne_zero'.2 (b0_normalizes (G:=G) ▸ (Gauge.slopeConstant_pos hg)))
  apply hx.congr'
  exact hp.mono fun i he=> by
    unfold regulatorRun
    simp only [Function.comp_apply,Real.sqrt_div' _ he.le ] -- replace namespace
    rw [inv_div,div_eq_mul_inv,mul_comm]
    rfl
end YM.Pert.Asymptotics
