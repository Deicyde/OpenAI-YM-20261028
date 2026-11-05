import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Selection
import YM.Further.FREE_COVARIANCE_KP.KP.Gem
import YM.Next.RANK.Concord
import YM.Next.RANK.Flux.Chronicle
import YM.Push.FREE_RESOLVENT.Atlas

/-!
# Losing temperature for changing connectors is for free

only at new Healthy smaller threshold. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source Source.Drops Thirst Baler Lattice Wilson MeasureTheory Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration Glimmer
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side}{b J k i N p d:ℕ} {C:Family G} {t a g δ:ℝ}
lemma pole_coal (J : ℕ)(z:ℝ)(C:Family G)(hG:G.Simple)(H:C.Makes): ∀ᶠ k:ℕ in atTop,
    ∀ N,k ≤ N→∀ p,
     let b:=sizeQ C k; let A:= C.path.levels; let s:=clim A k;let t:=tau A k;let g:=GaugeScale C k N p
     J*(max 1 (t/g))^J*(g⁻¹*(2*(2*G.colorScale*((4*b+2)* (4*b*t)))*t)) ≤ Perch.bill z s := by
    let y:=z-J-6; let A:=C.path.levels
    have hL : J+(1+1+y+1:ℝ)<z:=by unfold y;linarith only
    let γ:=G.colorScale; have hγ:0<γ:=G.colorScale_pos
    filter_upwards [booth A (-y) hG,(hat_rate A hG).eventually (hotter 1 zero_lt_one),
       setter C 1 zero_lt_one 8 hG H 1,(hat_rate A hG).eventually (transports hL (((J:ℝ)*4^J)* (2*(2*γ * (8*4))*4)))] with k hx hz hs ht N hN p
    intro b A' s t g
    have hp:0<g:= inv_pos.mpr (Real.sqrt_pos.2 (Overlay.beta_positive H.wilson hN)) -- fix
    let B:= Perch.bill 1 s;let r:= Perch.bill y s; let e:= A.clock.threshold k
    have hB:1≤B:= Glimmer.costed _ _ zero_le_one; have hr:0≤r:=(Real.exp_pos _).le
    have hy : e ≤ r:=by change A.clock.threshold k ≤ _; rw [neg_neg] at hx; exact hx
    have he : t ≤ e:= by change A.clock.hatCoupling k * hot s ≤ _; unfold e Calendar.threshold; rw [fire_bill]; exact mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (Real.sqrt_nonneg _))
    have hu : t/g ≤ 4*B:= by
       apply le_trans (div_le_div_of_nonneg_right he hp.le); have ht := Price.shrink_min C H hN p; unfold Price.shrink at ht; rw [inv_div,fire_bill] at ht; exact ht.trans (by change 2*B≤4*B;linarith only [hB])
    have ht':0≤t:=(tau_pos A k).le
    have h1:(b:ℝ) ≤ B:= by rw [pow_one] at hs; change 8*_≤ B at hs; change _ ≤ B; linarith only [hs,hB] -- contains sizeQ+1
    let f:=2*(2*γ*((4*(b:ℝ)+2)*(4*b*t)))
    have h2 : f ≤ 2*(2*γ * ((8*B)*(4*B*r))) := by
        dsimp only [f]; apply mul_le_mul_of_nonneg_left _ (by norm_num); apply mul_le_mul_of_nonneg_left _ (by positivity); refine mul_le_mul ?_ (mul_le_mul ?_ (he.trans hy) ht' (by positivity)) (by positivity) (by linarith); · linarith only [h1,hB]
        gcongr
    have h3 : (max 1 (t/g))^J ≤ 4^J*(B^J):= by rw [← mul_pow]; exact pow_le_pow_left₀ (zero_le_one.trans (le_max_left ..)) (max_le (by linarith only [hB]) hu) _
    change (J:ℝ)* _* (g⁻¹*(f*t))≤_
    rw [mul_left_comm g⁻¹ f t,← div_eq_inv_mul]
    refine le_trans ((mul_le_mul (mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg _)) (mul_le_mul h2 hu (by positivity) (by positivity)) (by unfold f; positivity) (by positivity))) ?_; refine le_trans ?_ ht; apply le_of_eq; change (J:ℝ)*(4^J*B^J)*(2*(2*γ*(8*B*(4*B*r)))*(4*B))=_*Perch.bill _ s; unfold r B; rw [bills,one_mul]; rw [← overlap,← overlap,←overlap,←overlap]; ring_nf
end YM.Next.Rank.East
