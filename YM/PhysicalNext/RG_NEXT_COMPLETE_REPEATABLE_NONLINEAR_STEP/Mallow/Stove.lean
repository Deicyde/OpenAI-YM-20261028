import YM.Further.DENSE_MIXED_KERNELS.Surface
import YM.Further.THRESHOLD_SOURCE_RESTART.Capital
import YM.Next.MAXWELL.Shelves
import YM.PhysicalNext.ORDERED_AFFINE_2B.SymSeason
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Turn.Wheels

/-!
 # λ pack exponent renewal payments. Prepack-mark shadow, not settled quote from scalar payout.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Mallow
open Function Filter Set Lattice Wilson RG Ovens Ovens.Pipes MeasureTheory Work.H03
open   Pressure Progress.DirectedRecipe Rack ConnectedActivityE6 Finset Push Push.AbsoluteSums
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G:Gauge}(L : Side){P: Teller G}(Q : ConnectedActivityE6.Target G P) {μ : ℝ}

-- relative template.D

def lauge (L : Side) (v : ℝ)(x C:ℝ) (_G:Gauge) := Real.exp (-v*C* (Delay.fineMonitor _G L x)^2)

lemma infuso (D c v:ℝ)(h:0<c)(hv:0<v)(a:ℝ) : Rate G L a (fun x=> D*lauge L c x v G):= by
  refine Rate.mul_left (?_) D -- order check
  have hp : Rate G L a (fun x=>Real.exp (-(c*v) * Delay.fineMonitor G L x ^ (2:ℝ))) := Rate.monitor_cutoff (mul_pos h hv) (by norm_num : 0<(2:ℝ))
  simpa only [Real.rpow_two, lauge,neg_mul] using! hp
set_option linter.unusedVariables false in
lemma mingle {C D : ℝ} (f:ℝ→ℝ) {a:ℝ} (ht:0<C) (he:0<D) (ha:a<0)(h:Rate G L a f) : ∀ᶠ x in atTop,
    ∀ u v:ℝ,0≤u→0≤v→ v ≤ f x→ u ≤D*lauge L C x 1 G→∃ κ:ℝ, Payments.Rates (radiusB x) (2*lauge L C x (1/2) G) u v κ:=by
  let t x:= lauge L C x (1/2) G
  have hα x:0 < t x:=Real.exp_pos _
  let V x:= (radiusB x+radiusB x+1:ℕ)
  have hV: Rate G L 0 (fun x=> (V x:ℝ)^4):=by unfold V; push_cast; simpa only [zero_mul] using! (((Rate.radius_price (G:=G) (L:=L)).add Rate.radius_price).add (Rate.const 1)).pow 4
  have hz:Rate G L a (fun x=> (V x:ℝ)^4*(D*t x+2*f x)):= by simpa only [zero_add] using! hV.mul ((infuso L D _ _ ht (by norm_num : (0:ℝ)<1/2) _).add (h.mul_left 2))
  filter_upwards [hz.below ha 1 zero_lt_one,h.below ha 1 zero_lt_one] with x H hz u v hu hv hh hx
  let κ:= (C/2)* (Delay.fineMonitor G L x)^2; have he:0≤κ:= by unfold κ; positivity
  have hc : Real.exp (-κ)=t x:=by unfold κ t lauge; ring_nf
  let p:= Payments.inflation u v κ
  have hP:0≤p:=by unfold p Payments.inflation; positivity
  have hk : (V x:ℝ)^4*p≤1:=by
    have hm : Real.exp κ*u ≤ D*t x:=by
      apply (mul_le_mul_of_nonneg_left hx (Real.exp_pos _).le).trans_eq
      unfold t lauge κ; rw [mul_left_comm,← Real.exp_add]; ring_nf
    exact (mul_le_mul_of_nonneg_left (add_le_add hm (mul_le_mul_of_nonneg_left hh zero_le_two)) (by positivity)).trans ((le_abs_self _).trans H)
  refine ⟨κ,he,hu,hv,hh.trans ((le_abs_self _).trans hz),hk,?_⟩
  have hp : p ≤ 1:= le_trans (le_mul_of_one_le_left hP (one_le_pow₀ (a:=(V x:ℝ)) (show 1≤(V x:ℝ) from by unfold V; norm_cast; omega))) hk
  have hh := Real.abs_exp_sub_one_le (x:=p) (by rw [abs_of_nonneg hP]; exact hp); rw [abs_of_nonneg hP] at hh
  have hv : Real.exp p -1 ≤ 2:= ((le_abs_self _).trans hh).trans (by linarith : 2*p ≤ 2)
  change Real.exp (-κ)* _ ≤ 2*t x; rw [hc]; exact (mul_le_mul_of_nonneg_left hv (hα _).le).trans_eq (mul_comm ..)
-- assignment Mark B.extent
lemma syrup (μ x:ℝ): Real.exp (-Q.mark L μ x)=lauge L (μ/4) x 1 G:=by unfold lauge Target.mark Target.costs Buy.quote Delay.hatWin; ring_nf
end YM.PhysicalNext.Repeat.Mallow
