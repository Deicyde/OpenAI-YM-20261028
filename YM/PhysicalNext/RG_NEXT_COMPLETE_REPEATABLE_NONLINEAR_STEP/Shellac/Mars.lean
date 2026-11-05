import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Shellac.Turmeric
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Sienna.Nuts
/-! # Price on seam Fmiot; `launchA`. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented Lapis Lantern Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Sienna Token
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {L : Side} {σ C : ℝ} {D : Patch} {g u f w : ℝ→ℝ} {n:ℕ}
local notation "s" => (fun t=> betaF G t L)
local notation "p₀" => (fun t=> (s t)^(-(2:ℝ)))
local notation "A" => eaves G L
lemma pole (V ν C' : ℝ) (_he : 0<V) (hv:0<ν) (h : Rate G L 0 f) (hu : Rate G L 0 g) (hr : Rate G L 0 u) (hw : Rate G L 0 w) (p:Clip) (J : BareRates.pre G σ C n) : ∀ᶠ t in atTop, ∀ a m κ β : ℝ,∀ c : Side, Stores.till t≤ c.val →
    a=g t*gStep β*gStep β+(p₀ t) → 1≤ u t → |κ|≤|C'| → 0 ≤ m → m ≤ V*w t → 0<β → β≤2*(s t) → s t/2 ≤ β → 0 ≤ kinBill n J p (u t) (f t)→0≤ BareRates.bill J p →
       a*(A t)+(p₀ t+p₀ t)+β*(kinBill n J p (u t) (f t)*(A t)^5)+ (cryo J p (u t) (f t) κ (w t)*(A t)^3+3*((p₀ t+a)*A t+tollS (u t) 2 (sailAmt (u t) G * (m *Real.exp (-ν*c.val)))*(A t)^2)) ≤ betaF G t L^ (-(23/20:ℝ)):= by
  let b t:=2*gStep (s t); let a t:= |g t| *b t*b t+p₀ t
  have he' : Rate G L (-(2:ℝ)) p₀:=Rate.power
  have ha : Rate G L (-1) a:= by
    refine Rate.add (((Brim.absolut hu).mul (glim G L)).mul (glim G L) |>.weaken (by norm_num)) (he'.weaken (by norm_num))
  have hW : Rate G L 0 (fun x=> wood n (f x)):= lumpRate n ((((Rate.const 1).add h)).add ((Rate.const 1).add h)) h
  have ht k (u':ℝ→ℝ) (hh:Rate G L 0 u') : Rate G L 0 (fun t=>tollS (u t) k (u' t)) := by simpa only [zero_mul,zero_add] using! (hr.pow k).mul hh
  let cC x:=kinBill n J p (u x) (f x)
  let p x:=cryo J p (u x) (f x) C' (w x)
  have hK: Rate G L 0 cC:= (ht _ _ (Rate.const _)).add hW
  have hc: Rate G L 0 p:= (ht n _ (((Rate.const (1+|C'|)).add hw).mul_right _)).add (hW.add h)
  let v t:= V* w t *Real.exp (-ν*Stores.till t); have hv' : Rate G L (-1) v:=by simpa only [zero_add] using! (hw.mul_left V).mul (Rate.cutoff (a:=-1) hv)
  let k t := tollS (u t) 2 (sailAmt (u t) G*v t); have hk : Rate G L (-1) k:= by unfold k sailAmt tollS; simpa only [zero_mul, zero_add] using! (hr.pow 2).mul (((((hr.pow 4).mul_right _).mul hr)).mul hv')
  let f' t:= a t*A t+(p₀ t+p₀ t)+2*s t*(cC t*(A t)^5)+(p t*(A t)^3+3*((p₀ t+a t)*A t+k t*(A t)^2))
  have hA:= Sienna.edge G L
  have hF: Rate G L (-(37/32)) f':=
    ((((ha.mul hA).weaken (by norm_num [vow])).add ((he'.add he').weaken (by norm_num))).add ((((Rate.hat (G:=G) (L:=L)).mul_left 2).mul (hK.mul (hA.pow 5))).weaken (by norm_num [vow]))).add (((hc.mul (hA.pow 3)).weaken (by norm_num [vow])).add ((((((he'.weaken (by norm_num : -(2:ℝ)≤ -1)).add ha).mul hA).weaken (by norm_num [vow])).add ((hk.mul (hA.pow 2)).weaken (by norm_num [vow]))).mul_left 3))
  filter_upwards [hF _ (show -(37/32:ℝ) < -(23/20:ℝ) by norm_num),Delay.shift_pos G L] with t ht hz i m κ β c hh hi hU hκ hm hv hb hβ hu hC hJ
  have hx:0 < A t:=Real.rpow_pos_of_pos hz _
  have hR := lamp G L hz β hu; have hi' : i ≤ a t:= by rw [hi]; apply add_le_add _ le_rfl; exact mul_le_mul (mul_le_mul (le_abs_self _) hR.2 hR.1.le (abs_nonneg _)) hR.2 hR.1.le (mul_nonneg (abs_nonneg _) (hR.1.le.trans hR.2))
  apply le_trans (b:= f' t) _ ((le_abs_self _).trans ht)
  have hh': m* Real.exp (-ν * c.val) ≤ v t:=mul_le_mul hv (Real.exp_monotone (mul_le_mul_of_nonpos_left (by exact_mod_cast hh) (neg_nonpos.mpr (by linarith)))) (Real.exp_pos _).le (hm.trans hv)
  have hS:0 ≤ sailAmt (u t) G:=by unfold sailAmt; positivity
  apply add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_right hi' hx.le) le_rfl) (mul_le_mul_of_nonneg_right hβ (mul_nonneg hC (pow_pos hx _|>.le)))) (add_le_add (mul_le_mul_of_nonneg_right ?_ (pow_pos hx _|>.le)) (mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right (add_le_add le_rfl hi') hx.le) (mul_le_mul_of_nonneg_right ?_ (pow_pos hx _|>.le))) (by norm_num)))
  · unfold p cryo tollS; gcongr
  unfold k tollS; gcongr
end YM.PhysicalNext.Repeat.Shellac
