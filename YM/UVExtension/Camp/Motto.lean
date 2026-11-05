import YM.UVExtension.Camp.Pin

/-! Real band on path-only predictor row.
No joint bends in bar-calendar, just on trial parameters relative to fixed hats. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Camp
open Function Set Filter RG Lattice Wilson Precision
open Lamppost AnalyticBridge VerifiedReset Collection
open Oriel Push Push.AbsoluteSums Metric RG.Shoot
open scoped Topology ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} (h:G.Simple)(T:Levels G)
    (α:ℕ→ℝ) (N:ℕ)

def slope (T:Levels G) (α:ℕ→ℝ) (m:ℕ):ℝ:= T.clock.bar - ∑ i∈Finset.range m, α i

def flatTime (T:Levels G) := pulse T 0* soft/4
lemma flat_pos :0<flatTime T:= by unfold flatTime; have h:=pulse_pos T 0; unfold soft Oriel.rim; positivity
lemma flat_limit : flatTime T≤ T.clock.bar/16:=by
   unfold flatTime; have ht:= pulse_falls T 0; simp only [Calendar.hatBeta,Schedule.scale_zero,mul_zero,add_zero] at ht; unfold soft Oriel.rim; linarith only [ht,T.clock.bar_pos]

variable {α N} (hD:Drifting T)(he: ∀ m, m<N → |α m+ G.slopeConstant*Real.log (T.S.block m).val|+1≤ (T.params (m+1)).drift)
include hD
lemma rough (i:ℕ): (T.params (i+1)).drift ≤ (G.slopeConstant/4)*Real.log (T.S.block i).val:= (div_le_iff₀ (logs_pos T i)).mp (hD i)
lemma traces {β:ℕ→ℝ} {δ:ℝ} (ho : |β 0-T.clock.bar|≤δ) (hp:∀ i, i<N → |β (i+1)-β i-G.slopeConstant*Real.log (T.S.block i).val| ≤ (T.params (i+1)).drift){m:ℕ}(hx:m≤N):|β m-T.clock.hatBeta m|≤ δ+(G.slopeConstant/4)*T.S.scale m:= by
    induction m with
    | zero => simpa [Calendar.hatBeta] using ho
    | succ i ih =>
      have hh:|β i - T.clock.hatBeta i|≤ _:= ih (by omega)
      let s:= T.S; let a:= β i-T.clock.hatBeta i; let b:= β (i+1)-β i-G.slopeConstant*Real.log (s.block i).val
      rw [Schedule.scale_succ, mul_add,← add_assoc, show β (i+1)-T.clock.hatBeta (i+1)=a+b from ?_]
      · exact (abs_add_le a b).trans (add_le_add hh ((hp _ hx).trans (rough T hD i)))
      unfold a b s Calendar.hatBeta; rw [Schedule.scale_succ]; unfold Levels.S; ring
omit hD
lemma first (T:Levels G): Camp.slope T α 0=T.clock.bar:=by simp [slope]
lemma plus (T:Levels G)(m:ℕ): Camp.slope T α (m+1)+α m= Camp.slope T α m:=by unfold slope; rw [Finset.sum_range_succ]; ring
include h hD
lemma known {β:ℕ→ℝ}(ho:|β 0-T.clock.bar|≤ flatTime T) (F:∀ i,i<N→ |β (i+1)-β i-G.slopeConstant*Real.log (T.S.block i).val| ≤ (T.params (i+1)).drift){m:ℕ}(hm:m≤N): InsideB (T.clock.hatBeta m) (β m):=by
    have hz:= abs_le.mp (traces T hD ho F hm); have hp:= Gauge.slopeConstant_pos h; have hv:= scale_nn T m; have hT:= flat_limit T
    unfold InsideB Calendar.hatBeta; unfold Calendar.hatBeta at hz
    have hx := mul_nonneg hp.le hv; constructor <;> linarith only [hz.1,hz.2,hx,hT,T.clock.bar_pos]
include he
lemma planned {m:ℕ}(hm:m≤N): InsideB (T.clock.hatBeta m) (Camp.slope T α m):=by
    refine known h T hD (β:=Camp.slope T α) (by rw [first,sub_self,abs_zero]; exact (flat_pos T).le) (fun i hi=>?_) hm
    rw [show _-Camp.slope T α i-G.slopeConstant*Real.log (T.S.block i).val=-(α i + G.slopeConstant*Real.log (T.S.block i).val) by linarith only [plus (α:=α) T i],abs_neg]
    linarith only [he i hi]
omit h hD he
lemma speaks (T:Levels G)(m:ℕ){u x:ℝ}(hu:InsideB (T.clock.hatBeta m) u)(hx: |x| ≤rim):
     u+pulse T m*x ∈ band T m:=by
  let v:=T.clock.hatBeta m; have h:1<v:=T.fits.delayed m; have hp:0< pulse T m:= pulse_pos ..
  have he: |pulse T m*x|≤ v/8:=by rw [abs_mul,abs_of_pos hp]; refine le_trans (mul_le_mul (pulse_falls ..) hx (abs_nonneg x) (zero_lt_one.trans h).le) ?_; unfold rim; linarith
  rw [abs_le] at he; change v/2≤_ ∧_≤2*v; constructor <;> linarith only [hu.1,hu.2,he.1,he.2,h]
lemma levy (h:G.Simple)(hf: Fees T) (m:ℕ): ∑ i∈Finset.range m,worth T (i+1)≤ pulse T m*(soft/4) := by
   apply le_trans _ (mul_le_mul_of_nonneg_left (budget_sum hf (Finset.range m)) (pulse_pos T m).le)
   rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i hi; have hz(i): worth T (i+1)= pulse T (i+1)*budget T (i+1):= by unfold budget; field_simp [(pulse_pos ..|>.ne')]
   exact (hz i).trans_le (mul_le_mul_of_nonneg_right (pulse_mono T h (Finset.mem_range.mp hi)) (hf.1 i))
end YM.UVExtension.Camp
