import YM.Gauge.Size
import YM.Shoot.Criteria


/-!
# Normalization and comparison in the *output* leg

Direct estimates on the actual tagged block kernel. No use of near-flat
or single-frame replacement. Gives a logarithmic-in-beta upper cost (per
bond, nonnegative band; useful even for very sharp noise) and strict
finite-volume floors (possibly exponentially small in beta times volume;
NOT offering the latter to pay a schedule or clustered remainder). Output
local log variation even for the interacting mixture. No corresponding
claim here for a *fine* leg (eligibility and shared frame switches).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SectorNext.Vacuum
open MeasureTheory Lattice Wilson RG Filter Set
open scoped Matrix.Norms.Frobenius BigOperators Topology Classical

variable {G : Gauge} {c f : Side} (S : StepData c f)

/-- Per-bond price range after multiplication by coupling. -/
def kick (β : ℝ) : ℝ := |β| * (2 * S.kernel.penalty)



private lemma pw_bounds (β : ℝ) (u : G.El) : Real.exp (-kick S β) ≤ S.penaltyWeight β u ∧
    S.penaltyWeight β u ≤ Real.exp (kick S β) := by
  have h := G.price_range u; have he := S.kernel.penalty_pos
  unfold StepData.penaltyWeight
  have hl : |-β * S.kernel.penalty * G.price u| ≤ kick S β := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_pos he, abs_of_nonneg h.1]
    unfold kick; rw [mul_comm 2, ← mul_assoc]; gcongr; exact h.2
  exact ⟨Real.exp_le_exp.mpr (abs_le.mp hl).1, Real.exp_le_exp.mpr (abs_le.mp hl).2⟩

private lemma pw_int (β : ℝ) : Integrable (S.penaltyWeight β) G.probHaar :=
    (S.penaltyWeight_cont β).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem pZ_bounds (β : ℝ) : Real.exp (-kick S β) ≤ S.penaltyZ β G ∧
    S.penaltyZ β G ≤ Real.exp (kick S β) := by
  constructor
  · have h := integral_mono (μ:=G.probHaar) (integrable_const (Real.exp (-kick S β)))
      (pw_int S β) (fun u => (pw_bounds S β u).1)
    simpa [StepData.penaltyZ] using h
  have h := integral_mono (μ:=G.probHaar) (pw_int S β) (integrable_const (Real.exp (kick S β)))
    (fun u => (pw_bounds S β u).2)
  simpa [StepData.penaltyZ] using h

/-- Actual radius r shell contribution to the noise normalizer, useful as
r shrinks with coupling. Note ambient dimension (color constants only). -/
theorem shell_pZ (β : ℝ) (r : ℝ) (hr : 0 < r) (hl : r ≤ 1) :
    (r/4)^Module.finrank ℝ G.Mat * Real.exp (-|β| * S.kernel.penalty * r^2 / 2) ≤ S.penaltyZ β G := by
  let a := Real.exp (-|β| * S.kernel.penalty * r^2 / 2)
  have h (u : G.El) (hu : u ∈ G.shell r) : a ≤ S.penaltyWeight β u := by
    have hg := (G.chord_price u)
    have hp : G.price u ≤ r^2/2 := by
      have hh := pow_le_pow_left₀ (G.chord_nonneg u) (show G.chord u ≤ r from hu) 2
      rw [hg] at hh; linarith
    have hy : 0 ≤ G.price u := (G.price_range u).1
    have hw : β * (S.kernel.penalty * G.price u) ≤ |β| * (S.kernel.penalty * (r^2/2)) := by
      have := S.kernel.penalty_pos
      gcongr; exact le_abs_self _
    unfold a StepData.penaltyWeight; apply Real.exp_le_exp.mpr; linarith
  apply (mul_le_mul_of_nonneg_right (G.shell_ge _ hr hl) (Real.exp_pos _).le).trans
  have H : ∀ u : G.El,(G.shell r).indicator (fun _ => a) u ≤ S.penaltyWeight β u := by
    intro u; by_cases hu : u ∈ G.shell r
    · rw [indicator_of_mem hu]; exact h u hu
    rw [indicator_of_notMem hu]; exact (Real.exp_pos _).le
  change G.probHaar.real _ * a ≤ _
  simpa [StepData.penaltyZ, integral_indicator (G.shell_meas _), setIntegral_const] using
    (integral_mono (μ:=G.probHaar) ((integrable_const a).indicator (G.shell_meas _)) (pw_int S β) H)

/-- Post-coupling but pre-torus per-bond cost; log beta growth on the
nonnegative band. (Use ambient finrank from actual shell lemma. No LocalRatio
or continuum identification needed.) -/
def shellBill (G : Gauge) (S : StepData c f) (β : ℝ) :=
  S.kernel.penalty / 2 + Module.finrank ℝ G.Mat * Real.log (4*(1+|β|))



theorem pZ_lo (β : ℝ) : Real.exp (- shellBill G S β) ≤ S.penaltyZ β G := by
  let r := (1+|β|)⁻¹
  have hx : 1 ≤ 1+|β| := by linarith [abs_nonneg β]
  have he : 0<1+|β| := zero_lt_one.trans_le hx
  have hl : 0<r := inv_pos.mpr he
  have ht : r ≤ 1 := inv_le_one_of_one_le₀ hx
  apply le_trans _ (shell_pZ S β r hl ht)
  have hs : Real.log (4*(1+|β|)) = -Real.log (r/4) := by
    rw [← Real.log_inv]; congr 1; simp [r]
  unfold shellBill; rw [hs]
  let d := Module.finrank ℝ G.Mat
  change Real.exp (-(_+(d:ℝ)*_)) ≤ _
  rw [show -(S.kernel.penalty/2+(d:ℝ)* -Real.log (r/4)) = (d:ℝ)* Real.log (r/4) + (-S.kernel.penalty/2) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log (by positivity)]
  gcongr
  have h : |β| *r ≤ 1 := (mul_le_mul_of_nonneg_right (show |β| ≤ 1+|β| by linarith) hl.le).trans
    (mul_inv_cancel₀ he.ne').le
  have h' := mul_le_one₀ h hl.le ht
  have hg := S.kernel.penalty_pos
  nlinarith only [mul_le_mul_of_nonneg_right h' hg.le]





/-- Kernel floor and ceiling apply to every field and always after tag
averaging, even when all but one of the shared tag outcomes vanish. -/
def wires (c : Side) : ℝ := Fintype.card (Edge (Site c))

private lemma from_noise (h : S.patch.Branches S.kernel G) (β : ℝ) (a b : ℝ)
    (hA : ∀ u : G.El, Real.exp a ≤ (S.penaltyZ β G)⁻¹ * S.penaltyWeight β u)
    (hB : ∀ u : G.El, (S.penaltyZ β G)⁻¹ * S.penaltyWeight β u ≤ Real.exp b) (U : Config G f) (V : Config G c) :
    Real.exp (wires c*a) ≤ S.density β U V ∧ S.density β U V ≤ Real.exp (wires c*b) := by
  have hp (u : G.El) : 0 ≤ (S.penaltyZ β G)⁻¹ * S.penaltyWeight β u := (Real.exp_pos a).le.trans (hA u)
  have he (Q : Config G c) : Real.exp (wires c*a) ≤ S.noise β Q V := by
    simpa only [Finset.prod_const, Finset.card_univ, wires, Real.exp_nat_mul, StepData.noise] using
      (Finset.prod_le_prod (s:=Finset.univ (α:=Edge (Site c))) (f:=fun _=>Real.exp a) (fun _ _ => (Real.exp_pos a).le)
        (fun x _ => hA (V x * (Q x)⁻¹)))
  have hg (Q : Config G c) : S.noise β Q V ≤ Real.exp (wires c*b) := by
    simpa only [Finset.prod_const, Finset.card_univ, wires, Real.exp_nat_mul, StepData.noise] using
      (Finset.prod_le_prod (s:=Finset.univ (α:=Edge (Site c))) (fun x _ => hp (V x * (Q x)⁻¹)) (g:=fun _ => Real.exp b)
        (fun x _ => hB (V x * (Q x)⁻¹)))
  constructor
  · calc
      _ = ∑ t, S.likelihood U t * Real.exp (wires c*a) := by rw [←Finset.sum_mul,S.chosen h U, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (he _) (S.likelihood_pos U t)
  calc
    _ ≤ ∑ t, S.likelihood U t * Real.exp (wires c*b) := Finset.sum_le_sum fun t _ =>
      mul_le_mul_of_nonneg_left (hg _) (S.likelihood_pos _ _)
    _ = _ := by rw [←Finset.sum_mul,S.chosen h U,one_mul]

theorem density_range (h : S.patch.Branches S.kernel G) (β : ℝ) (U : Config G f) (V : Config G c) :
    Real.exp (-(wires c*(2*kick S β))) ≤ S.density β U V ∧
      S.density β U V ≤ Real.exp (wires c*(shellBill G S β+kick S β)) := by
  let z := S.penaltyZ β G
  have hz : 0 < z := S.penaltyZ_pos β
  rw [←mul_neg]
  refine from_noise S h β _ _ (fun u => ?_) (fun u=> ?_) U V
  · rw [show -(2*kick S β)=-kick S β + -kick S β by ring, Real.exp_add]
    refine mul_le_mul ?_ (pw_bounds S β u).1 (Real.exp_pos _).le (inv_pos.mpr hz).le
    rw [Real.exp_neg]; exact inv_anti₀ hz (pZ_bounds S β).2
  rw [Real.exp_add]; refine mul_le_mul ?_ (pw_bounds S β u).2 (Real.exp_pos _).le (Real.exp_pos _).le
  simpa only [Real.exp_neg,inv_inv] using (inv_anti₀ (Real.exp_pos _) (pZ_lo S (G:=G) β))




omit S in
lemma price_compare (u v : G.El) : |G.price u-G.price v| ≤ 2*G.chord (u*v⁻¹) := by
  have h := G.chord_triangle (u*v⁻¹) v
  rw [mul_assoc, inv_mul_cancel, mul_one] at h
  have he := G.chord_triangle (u*v⁻¹)⁻¹ u
  rw [G.chord_inv (u*v⁻¹),mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] at he
  have hp := G.chord_price u; have hk := G.chord_price v
  have h0 := G.chord_nonneg u; have h1 := G.chord_nonneg v
  have hu := G.chord_le_two u; have hv := G.chord_le_two v
  rw [show G.price u-G.price v=(G.chord u-G.chord v)*(G.chord u+G.chord v)/2 by linarith,abs_div,abs_mul,abs_of_nonneg (by linarith : 0≤G.chord u+G.chord v)]
  norm_num
  have hh := mul_le_mul (show |G.chord u-G.chord v| ≤ G.chord (u*v⁻¹) from abs_le.mpr ⟨by linarith,by linarith⟩) (show G.chord u+G.chord v≤4 by linarith) (show 0≤G.chord u+G.chord v by linarith) (G.chord_nonneg _)
  linarith











/-- The actual fine mass (includes any scalar F carries). -/
def vacuumMass {n : Side} (F : Config G n → ℝ) := ∫ U, F U ∂prior G n

private theorem push_range_aux (h : S.patch.Branches S.kernel G) (β : ℝ) (a b : ℝ) (F : Config G f → ℝ)
    (hi : Integrable F (prior G f)) (hn : ∀ U, 0 ≤ F U) (V : Config G c)
    (he : ∀ U, Real.exp (-a) ≤ S.density β U V ∧ S.density β U V ≤ Real.exp b) :
    Real.exp (-a)*vacuumMass F ≤ S.push β F V ∧ S.push β F V ≤ Real.exp b*vacuumMass F := by
  unfold vacuumMass StepData.push
  constructor <;> rw [← integral_const_mul]
  · exact integral_mono (hi.const_mul _) (StepData.push_slice (S.isKernel h β) V F hi) fun U => mul_le_mul_of_nonneg_right (he U).1 (hn U)
  exact integral_mono (StepData.push_slice (S.isKernel h β) V F hi) (hi.const_mul _) fun U => mul_le_mul_of_nonneg_right (he U).2 (hn U)

theorem push_sandwich (h : S.patch.Branches S.kernel G) (β : ℝ) (F : Config G f → ℝ)
    (hi : Integrable F (prior G f)) (hn : ∀ U, 0 ≤ F U) (V : Config G c) :
    Real.exp (-(wires c*(2*kick S β)))*vacuumMass F ≤ S.push β F V ∧
      S.push β F V ≤ Real.exp (wires c*(shellBill G S β+kick S β))*vacuumMass F :=
  push_range_aux S h β _ _ F hi hn V fun U => density_range S h β U V



theorem push_pos (h : S.patch.Branches S.kernel G) (β : ℝ) (F : Config G f → ℝ)
    (hi : Integrable F (prior G f)) (hn : ∀ U, 0 ≤ F U) (hl : 0 < vacuumMass F) (V : Config G c) :
    0 < S.push β F V := (mul_pos (Real.exp_pos _) hl).trans_le (push_sandwich S h β F hi hn V).1







end YM.SectorNext.Vacuum
