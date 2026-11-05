import YM.Next.MULTISOURCE.Tariff


/-!
# Tariff and marker radius
-/
set_option autoImplicit false
noncomputable section
namespace YM.Multi
open RG Wilson Filter Function Finset Source Labels Mix Stock
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge}

/-- Include in level-planning purchases. Needed for the fixed-footprint
banking at the common support exponent. -/
def Margins (A : Levels G) := ∃ M : ℕ, ∀ᶠ i in atTop, (A.params i).supportExponent ≤
    M * Real.log (A.clock.hatBeta i)

namespace Wage

variable (C : Family G)

def tab (i : ℕ) := ∏ k∈Finset.range i,(C.path.levels.params (k+1)).columns
lemma tab_ge (i : ℕ) : 1 ≤ tab C i := Finset.one_le_prod fun _ _ => (C.path.levels.params _).columns_ge

lemma hat_tend (h : G.Simple) (A : Levels G) : Tendsto A.clock.hatBeta atTop atTop :=
  tendsto_atTop_add_const_left _ _ (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
lemma log_tend (h : G.Simple) (A : Levels G) : Tendsto (Real.log ∘ A.clock.hatBeta) atTop atTop :=
  Real.tendsto_log_atTop.comp (hat_tend h A)
lemma small_hat (h : G.Simple) (A : Levels G) : Tendsto A.clock.hatCoupling atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp (hat_tend h A))

lemma benefit {N p j d : ℕ} (H : C.Makes) (v : C.label d) (h : C.ref d ≤ j) (hx : j ≤ N) :
    (C.labels.level d).coeffSize (Single.coeff C N p j v).x ≤ tab C j*(C.labels.level d).coeffSize v := by
  have hc := H.calibrated d N p (h.trans hx)
  let F := C.labels.level d
  induction j,h using Nat.le_induction with
  | base =>
    have he : (Single.coeff C N p (C.ref d) v).x=v := C.normalized H hx v
    rw [he]
    exact le_mul_of_one_le_left (Work.G08.size_nonneg F v) (tab_ge ..)
  | succ j hj ih =>
    let r := (C.path.levels.params (j+1)).columns
    apply le_trans (show F.coeffSize (Single.coeff C N p (j+1) v).x ≤ r*F.coeffSize (Single.coeff C N p j v).x from
      hc.back j hj hx _)
    rw [show tab C (j+1)=tab C j*r from Finset.prod_range_succ ..]
    refine (mul_le_mul_of_nonneg_left (ih (by omega)) (show 0≤r from zero_le_one.trans (C.path.levels.params _).columns_ge)).trans_eq ?_
    ring

lemma canvas (i : ℕ) : Mix.envelope C 1 i = (C.path.levels.params i).columns*tab C i := by simp [Mix.envelope,tab]

lemma width_positive (i k : ℕ) : 0 < width C 1 k i := by
  unfold width; rw [canvas]
  exact div_pos (pow_pos (potential_hat ..).1 k) (mul_pos
    (lt_of_lt_of_le zero_lt_one (C.path.levels.params i).columns_ge) (zero_lt_one.trans_le (tab_ge ..)))

/-- One exponent sufficient for all eventual uses of the fixed engineering d
on bounded coefficients. Doesn't require a schedule purchase depending on R. -/
lemma reception (h : G.Simple) (H : C.Makes) (ht : Margins C.path.levels) (d : ℕ) :
    ∃ k : ℕ, ∀ R : ℝ, 0 ≤ R → ∀ᶠ i : ℕ in atTop, ∀ N p : ℕ, i ≤ N →
      ∀ v : C.label d, (C.labels.level d).coeffSize v ≤ R →
      width C 1 k i * Single.tariff C N p i v ≤ 1/8 := by
  let A := C.path.levels
  obtain ⟨M,hM⟩ := ht
  let k := Maquette.maxgrade (C.labels.level d)
  let g := A.clock.hatCoupling
  have he : ∀ᶠ i : ℕ in atTop, Single.stipend C i ≤ Real.exp 2 *(g i)⁻¹^(2*M) := by
    filter_upwards [hM] with i hi
    let b := A.clock.hatBeta i
    have hb : 0 < b := zero_lt_one.trans (A.fits.delayed i)
    calc
      _ ≤ Real.exp (2+ M*Real.log b) := Real.exp_monotone (le_trans (add_le_add_left hi 2) (add_comm ..).le)
      _ = Real.exp 2 * b^M := by rw [Real.exp_add,Real.exp_nat_mul,Real.exp_log hb]
      _ = _ := by
        change _ = _ * (((Real.sqrt b)⁻¹)⁻¹ ^ _)
        rw [inv_inv, pow_mul, Real.sq_sqrt hb.le]
  refine ⟨k+2*M+1,fun R hR => ?_⟩
  let X := 2+Single.kitty C d
  let E := (1+R)*Real.exp 2*X
  have hg : ∀ᶠ i in atTop, g i*E ≤ 1/8 := by
    have ht : Tendsto (fun i => g i*E) atTop (𝓝 (0*E)) := (small_hat h A).mul_const E
    rw [zero_mul] at ht
    exact ht.eventually (ge_mem_nhds (by norm_num : (0:ℝ)<1/8))
  filter_upwards [eventually_ge_atTop (C.ref d),he,hg] with i hi he hε N p hN v hv
  let R' := (C.labels.level d).coeffSize (Single.coeff C N p i v).x
  let w := width C 1 (k+2*M+1) i
  have hc := (A.params i).columns_ge
  let u := tab C i
  have ho : 1 ≤ u := tab_ge ..
  have hU : 1+R' ≤ u*(1+R) := (add_le_add ho (le_trans
    (show R' ≤ u*_ from benefit C H v hi hN) (mul_le_mul_of_nonneg_left hv (zero_le_one.trans ho)))).trans_eq
    (by rw [mul_add,mul_one])
  have hX : 0≤X := add_nonneg (by norm_num) (Single.kitty_pos ..).le
  have hs : 0 < w := width_positive ..
  have hb : 0 < g i := (potential_hat ..).1
  refine le_trans ?_ hε
  unfold Single.tariff
  change w * ((1+R')*_*Single.stipend C i * (g i)⁻¹^k * X) ≤ g i * _
  calc
    _ ≤ w * ((u*(1+R))*(A.params i).columns * (Real.exp 2*(g i)⁻¹ ^(2*M)) * (g i)⁻¹ ^ k * X) := by
      have hi : 0 ≤ Single.stipend C i := zero_le_one.trans (Single.stipend_hi ..)
      have hh : 0 ≤ R' := Work.G08.size_nonneg ..
      gcongr
    _ = _ := by
      have hu := lt_of_lt_of_le zero_lt_one hc
      have hK : 0 < u := zero_lt_one.trans_le ho
      unfold w width E; rw [canvas]
      change _^_ / ((A.params i).columns*u)*_= _
      simp only [inv_pow,pow_add]
      change g i^k * g i^_ * g i^1 / _ * _ = _
      field_simp
end Wage
end YM.Multi
