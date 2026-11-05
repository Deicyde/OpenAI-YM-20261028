import YM.PertExtension.Interior
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Inverse Hessian and translations of the centered finite-dimensional Gaussian. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.PertExtension.GaussianScore
open Series Function Filter Set Metric MeasureTheory
open scoped Topology ContDiff Classical BigOperators
open LinearMap Radial

variable {E : Type*}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
local notation "V" => Module.Dual ℝ E
structure Law (E : Type*) [NormedAddCommGroup E][NormedSpace ℝ E] where
  P : E →ₗ[ℝ] (Module.Dual ℝ E)
  turns x y : P x y=P y x
  slope : ∃ c>0,∀ x, c*‖x‖^2 ≤ P x x/2
  smooth : Continuous (fun x : E=>P x x)

namespace Law
variable (Γ : Law E)
include Γ

def kern (x : E) := Real.exp (-(Γ.P x x)/2)
lemma continuous_kern : Continuous Γ.kern := Real.continuous_exp.comp (Γ.smooth.neg.div_const _)

private lemma inject : Function.Injective Γ.P := LinearMap.ker_eq_bot.mp (by
   refine le_bot_iff.mp fun x hx=> ?_
   have hx : Γ.P x=0 := hx
   obtain ⟨c,hc,H⟩:=Γ.slope
   specialize H x; simp_rw [hx] at H; change c*‖x‖^2 ≤ (0/2:ℝ) at H
   have he:‖x‖^2 ≤ 0 := by nlinarith only [hc,H]
   exact (show ‖x‖ ≤ 0 from by nlinarith [sq_nonneg ‖x‖]) |> (norm_le_zero_iff).mp)

def inverse : V →ₗ[ℝ] E :=
 (LinearEquiv.ofBijective Γ.P ⟨Γ.inject,(injective_iff_surjective_of_finrank_eq_finrank (by rw [Subspace.dual_finrank_eq])).mp Γ.inject⟩).symm.toLinearMap
@[simp] lemma applies ℓ : Γ.P (Γ.inverse ℓ)=ℓ := by apply (LinearEquiv.apply_symm_apply (LinearEquiv.ofBijective Γ.P _))
@[simp] lemma solves x : Γ.inverse (Γ.P x)=x := by apply Γ.inject;rw [Γ.applies]

local notation "Z" => Radial.zone (E:=E)
def wick (ℓ ℓ' : V) := ℓ' (Γ.inverse ℓ)

omit Γ in
lemma linearInvoice (ℓ : V) : Zone.Invoice Z ℓ :=
  ⟨⟨‖LinearMap.toContinuousLinearMap ℓ‖,1,norm_nonneg _,fun x=>((LinearMap.toContinuousLinearMap ℓ).le_opNorm x).trans (by rw [pow_one];gcongr;unfold Radial.zone; simp)⟩⟩

variable {A : E→ℝ}
lemma translation_bound (h : Zone.Invoice Z A) (v : E) :∃ c>0,∃ C>0,∃ e:ℕ, ∀ x (t:ℝ), |t| ≤ 1→
       ‖(A*Γ.kern) (x+t • v)‖ ≤ C*bill e c x := by
  obtain ⟨c,hc,H⟩:=Γ.slope
  obtain ⟨K,e,hK,h⟩:=h
  let r:=‖v‖+1
  let B:= (1+K)*r^e * Real.exp (c*‖v‖^2)
  have hr:0<r:=by unfold r; have:=norm_nonneg v;linarith
  have hB:0<B:=by unfold B; positivity
  refine ⟨c/2,half_pos hc,B,hB,e,fun x t ht=>?_⟩
  let y:=x+t • v
  have hty: ‖t • v‖ ≤ ‖v‖ := by rw [norm_smul,Real.norm_eq_abs];exact mul_le_of_le_one_left (norm_nonneg _) ht
  have hxy : ‖x‖ ≤ ‖y‖+‖v‖ := by rw (occs:=.pos [1]) [show x=y-t• v from (add_sub_cancel_right ..).symm]; exact (norm_sub_le ..).trans (add_le_add_right hty _)
  have hyx : ‖y‖≤‖x‖+‖v‖:= by unfold y; exact (norm_add_le ..).trans (add_le_add_right hty _)
  have hP : (c/2)*‖x‖^2≤ Γ.P y y/2+c*‖v‖^2 := by
     have hp:= H y
     have h' : ‖x‖^2 ≤ (‖y‖+‖v‖)^2:=by gcongr
     calc
       _ ≤ c*(‖y‖^2+‖v‖^2) := by have := mul_le_mul_of_nonneg_left h' hc.le; nlinarith only [mul_nonneg hc.le (sq_nonneg (‖y‖-‖v‖)),this]
       _ ≤ _ := by rw [mul_add];gcongr
  have he' : Γ.kern y≤Real.exp (c*‖v‖^2)*Real.exp (-(c/2)*‖x‖^2):=by
     rw [←Real.exp_add]; unfold kern;gcongr;linarith
  have ht':(Z).w y ≤ r*(Z).w x:=by change 1+_≤ (‖v‖+1)*(1+_);nlinarith only [mul_nonneg (norm_nonneg v) (norm_nonneg x), hyx]
  have hxZ : 0≤(Z).w x:= zero_le_one.trans ((Z).high x)
  have htZ : 0≤(Z).w y:= zero_le_one.trans ((Z).high y)
  have hk : 0≤Γ.kern y:=le_of_lt (Real.exp_pos _);

  calc
    _ ≤ (K*(Z).w y^e)*(Real.exp (c*‖v‖^2)*Real.exp (-(c/2)*‖x‖^2)) := by change ‖A y * Γ.kern y‖ ≤_;rw [norm_mul,Real.norm_eq_abs (Γ.kern y),abs_of_nonneg hk];exact mul_le_mul (h y) he' hk (by positivity)
    _ ≤ (K+1)*(r*(Z).w x)^e*(Real.exp _ * Real.exp _):= by gcongr;linarith
    _ = _ := by unfold B bill;rw [mul_pow]; ring

variable [MeasurableSpace E][BorelSpace E]
lemma integrable_entry (μ : Measure E)[μ.HasTemperateGrowth](h : Zone.Invoice Z A)(hA : Continuous A) : Integrable (A*Γ.kern) μ:= by
  obtain ⟨c,hc,C,hC,e,H⟩:=Γ.translation_bound h 0
  refine ((bill_integrable μ e hc).const_mul C).mono' (hA.mul Γ.continuous_kern).aestronglyMeasurable (Eventually.of_forall fun x=>?_)
  simpa using H x (0:ℝ) (by norm_num)
end Law
end YM.PertExtension.GaussianScore
