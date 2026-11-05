import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Group.IntegralConvolution
import YM.Analysis.Nonnegative
import YM.Cells.Tiling
import YM.Extraction.Orders
import YM.Overlay.Bill
import YM.Source.Construction

/-!
# Extensive bound independent of all R,N given envelopes

Can use stagewise C*(1+log hatBeta). Instead keep explicit formula (broader
allowed , can still demand a subpower of total σ). Producers need to
cover pure-marker costs at the joint stop; no implicit absorption in o(1) yet.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Vac
open Function Set Wilson Lattice RG Overlay Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff
variable {G : Gauge}

/-- Numerical expense per site ignoring source markers. -/
def treasury (A : Levels G) (m : ℕ) : ℝ :=
    let C := A.clock
    let r := (C.params m).paths
    let u := C.hatCoupling m
    let δ := C.allowance m
    let Λ := C.loopCap m
    let β := 2*C.hatBeta m
    2*(δ+PathData.loopsPrice (A.budget m) β r Λ)+ C.forcedAllowance m + β*baseBudget (A.params m).clip r u +
      4 * Module.finrank ℝ G.Mat * Real.log (16/u)

lemma suffices_bill {H : History G} {n N p} (h : H.Selected) (hn : n≤N) (q : ℕ) (u c d b : ℝ) :
    let C := H.levels.clock
    let r := (C.params n).paths
    Bands.finalBill q (H.rep N p n) (C.hatCoupling n) u c d b r (C.loopCap n)
        (C.allowance n) (C.forcedAllowance n) ≤
      Fintype.card (Site (C.schedule.side n p))* treasury H.levels n+q*(u+c+d*b) := by
  intro C r
  have hz := h.represents N p _ hn
  have he := hz.band.2
  unfold treasury Bands.finalBill Rep.exCost
  simp only [hz.vac,hz.clip]
  have hv : PathData.loopsPrice (H.levels.budget n) (H.β N p n) r (C.loopCap n) ≤
      PathData.loopsPrice (H.levels.budget n) (2*C.hatBeta n) r (C.loopCap n) := by
    unfold PathData.loopsPrice
    apply add_le_add_left
    have h := (H.levels.budget n).threshold_pos
    have ht : 0<r := (C.params n).paths_pos
    exact mul_le_mul_of_nonneg_right he (by positivity)
  have hb : 0≤ baseBudget (H.levels.params n).clip r (C.hatCoupling n) := by
    unfold baseBudget; have H := (H.levels.params n).clip.quadratic_pos; positivity
  gcongr

namespace Numbers

-- self-contained function for threshold gate instantiated later, freezes A
-- not arbitrary scale cost; useful in combination with ExpRead.
variable {X : ℝ}

lemma monitor (b : ℝ) : Tendsto (fun s : ℝ => b*(Real.log (Real.log s))^2 / Real.log s) atTop (𝓝 0) := by
  have ht := Real.isLittleO_pow_log_id_atTop (n:=2)
  simpa only [div_eq_mul_inv, Function.comp_def,id_eq,mul_zero, mul_assoc] using! ((ht.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop).const_mul b)

def Hat (s : ℝ) := (Real.sqrt s)⁻¹
def P (s : ℝ) := Real.exp (Real.log (Real.log s)^2)
def theta (s : ℝ) := Hat s * P s
lemma cost (b : ℝ) (p : ℝ) (hp : 0 < p) : ∀ᶠ s : ℝ in atTop, P s ^ b ≤ s ^ p := by
  filter_upwards [(monitor b).eventually (ge_mem_nhds hp),eventually_gt_atTop 1] with s h hs
  have he : b*(Real.log (Real.log s))^2 ≤ p*Real.log s := (div_le_iff₀ (Real.log_pos hs)).1 h
  rw [P, Real.exp_mul (Real.log _ ^2) b |>.symm, Real.rpow_def_of_pos (by linarith)]; apply Real.exp_monotone
  simpa [mul_comm] using he

/-- P/p scalar issue sampled at ANY smoothing index gives bounded choice
in (0,1); monitor ≥1. Verify even without θ gates.
-/
lemma uniform_loop : ∀ᶠ s : ℝ in atTop, s*(theta s)^2≤(P s)^2 ∧ s*(theta s)^3≤1 ∧ s*(theta s)^4≤1 ∧
    ∀ v : ℝ, v ≤ 1 → 2*(P s)^v*theta s^2 ≤ 1 := by
  have hh : ∀ᶠ s : ℝ in atTop, theta s≤1 := by
    filter_upwards [cost 1 (1/2:ℝ) (by norm_num),eventually_gt_atTop (1:ℝ)] with s h hs
    unfold theta Hat; rw [Real.rpow_one,←Real.sqrt_eq_rpow] at h
    have hn : 0<Real.sqrt s := Real.sqrt_pos.2 (by linarith)
    exact (mul_le_mul_of_nonneg_left h (by positivity)).trans (by rw [inv_mul_cancel₀ hn.ne'])
  filter_upwards [cost 3 (1/2:ℝ) (by norm_num), hh,eventually_ge_atTop 4] with s h hs he
  have hg : P s^ (3:ℕ) ≤ Real.sqrt s := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]; simpa using h
  have h0 : 0<Real.sqrt s := Real.sqrt_pos.2 (by linarith)
  have hh : (Real.sqrt s)^2=s := Real.sq_sqrt (by linarith)
  have ht : 0<theta s := mul_pos (by unfold Hat; positivity) (Real.exp_pos _)
  have H : s*theta s^2=P s^ (2:ℕ) := by unfold theta Hat; field_simp; rw [hh]
  have hi : s*theta s^3≤1 := calc
    _ = (P s^ (2:ℕ))*theta s := by rw [←H]; ring
    _ = (Real.sqrt s)⁻¹*P s^ (3:ℕ) := by unfold theta Hat; ring
    _ ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hg (by positivity)) (by rw [inv_mul_cancel₀ h0.ne'])
  refine ⟨H.le,hi,?_,fun v hV => ?_⟩
  · rw [pow_succ,←mul_assoc]; exact le_trans (mul_le_mul_of_nonneg_left hs (by positivity : 0≤s*theta s^3)) (by rwa [mul_one])
  have hx : P s^v≤P s := (Real.rpow_le_rpow_of_exponent_le (Real.one_le_exp (sq_nonneg _)) hV).trans (Real.rpow_one _).le
  apply le_of_mul_le_mul_left (a:=s) ?_ (by linarith : 0<s) -- binder ?
  calc
    _ ≤ s*(2*P s*theta s^2) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx (by positivity)) (by positivity)) (by linarith)
    _ = 2* P s^3 := by rw [show _*(2*_ * _^2)=(2*P s)*(s*theta s^2) by ring,H]; ring
    _ ≤ _ := by nlinarith
end Numbers

def fiat (G : Gauge) (A : Stage) (s : ℝ) :=
    2*(1+(4*A.paths+1))+ 1+(Fintype.card PlaqAxes:ℝ)*(A.clip.direct+A.paths^2) +
      4*Module.finrank ℝ G.Mat*(Real.log 16+Real.log s/2)

lemma treasury_stage (A : Levels G) (h : G.Simple) : ∀ᶠ m : ℕ in atTop,
    treasury A m ≤ fiat G (A.params m) (A.clock.hatBeta m) := by
  have he : Tendsto A.clock.hatBeta atTop atTop := Filter.tendsto_atTop_add_const_left _ _
    (A.S.divergent.const_mul_atTop (Gauge.slopeConstant_pos h))
  filter_upwards [he.eventually Numbers.uniform_loop] with m hm
  let a := A.clock
  let s := a.hatBeta m
  obtain ⟨-,h3,h4,hF⟩ := hm
  let b := a.stage (a.J m)
  have hn : 1<s := A.fits.delayed _
  have hx : a.loopCap m*(a.threshold m)^2≤1 := by
    refine hF _ ((A.fits.thetaRange m).2.trans ?_)
    have hy : (1:ℝ)≤A.clock.J m := by
      have ha := A.clock.adm m
      exact_mod_cast (by omega : 1 ≤ A.clock.J m)
    exact le_trans (inv_anti₀ zero_lt_one hy) (inv_one.le)
  have ht : (Real.sqrt s)^2=s := Real.sq_sqrt (by linarith)
  have hg : 0<a.hatCoupling m := inv_pos.mpr (Real.sqrt_pos.2 (by change 0<s; linarith))
  have hw : a.hatCoupling m ≤ 1 := by
    refine (inv_le_one_of_one_le₀ ?_)
    exact Real.le_sqrt_of_sq_le (by simpa using hn.le)
  have hP : PathData.loopsPrice (A.budget m) (2*s) b.paths (a.loopCap m) ≤ 4*b.paths+1 := by
    unfold PathData.loopsPrice;
    change (2*s)*(b.paths*(a.threshold m)^3+b.paths*(a.threshold m)^4) +_ ≤ _
    change s*(a.threshold m)^3≤1 at h3
    change s*(a.threshold m)^4≤1 at h4
    apply add_le_add _ hx
    · linarith only [mul_le_mul_of_nonneg_left h3 b.paths_pos.le,mul_le_mul_of_nonneg_left h4 b.paths_pos.le]
  have hn : a.forcedAllowance m ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr <| Real.rpow_nonneg (Real.exp_pos _).le _)
  have hb : a.allowance m≤1 := Real.rpow_le_one hg.le hw (by norm_num)
  have hy : s*(a.hatCoupling m)^2=1 := by change s*((Real.sqrt s)⁻¹)^2=1; have he := hg; unfold Calendar.hatCoupling at he; field_simp; linarith
  have hB : 2*s*baseBudget b.clip b.paths (a.hatCoupling m)=(Fintype.card PlaqAxes:ℝ)*(b.clip.direct+b.paths^2) := by unfold baseBudget; linear_combination (norm:=ring) (Fintype.card PlaqAxes:ℝ)*(b.clip.direct+b.paths^2)*hy
  have hl : Real.log (16/a.hatCoupling m)=Real.log 16+Real.log (Real.sqrt s) := by rw [Real.log_div (by norm_num) hg.ne']; unfold Calendar.hatCoupling; rw [Real.log_inv,sub_neg_eq_add]
  unfold treasury fiat; dsimp only
  have HL : Real.log (16/A.clock.hatCoupling m)=Real.log 16+Real.log s/2 := by rw [show A.clock=a from rfl,hl,Real.log_sqrt (by nlinarith only [ht,sq_nonneg (Real.sqrt s)])]
  rw [show (2*A.clock.hatBeta m)*_=(Fintype.card PlaqAxes:ℝ)*(b.clip.direct+b.paths^2) from hB, HL]; gcongr
end YM.Vac
