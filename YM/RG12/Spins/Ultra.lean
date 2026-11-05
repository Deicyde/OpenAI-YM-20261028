import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Pieces
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Cues
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Chant
/-!
# Post-block analytic gate for all exponent demands. PP here is about
numerical pieces as functions of the legal parameter x = hatBeta m,
not S encounters/UV periods. Stage constants fixed while issuing the
demand, to be bought again in every chapter used.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Spins
open Function Filter Set Lattice RG Pressure Wilson AnalyticBridge.LocalGaussianLaws.Lift PhysicalNext.JointLoad.Heir
open scoped Topology BigOperators Classical
-- Strong enough for powers of g after any admitted statistical estimates
def Super (f:ℝ→ℝ):Prop := ∀ p:ℕ, ∀ᶠ x:ℝ in atTop, |f x| ≤ (x^p)⁻¹
lemma tender_nat {t:ℝ} (ht:0<t) (p:ℕ): ∀ᶠ x:ℝ in atTop, Real.exp (-t*(radiusB x:ℝ)) ≤ (x^p)⁻¹ := by
    open Extra.Iteration.Scales in
      filter_upwards [Extra.Iteration.Scales.first t (p:ℝ) ht, eventually_ge_atTop (0:ℝ)] with x h hx
      rw [Real.rpow_neg hx,Real.rpow_natCast] at h; exact h
lemma horizon_nat {t:ℝ} (ht:0<t)(p:ℕ):∀ᶠ x:ℝ in atTop, Real.exp (-t*(Stores.till x:ℝ)) ≤ (x^p)⁻¹ := by
    filter_upwards [plume t (p:ℝ) ht, eventually_ge_atTop (0:ℝ)] with x h hx
    rw [Real.rpow_neg hx,Real.rpow_natCast] at h; exact h
-- enough generic polynomial cost gate for after-block constants independent of x
lemma super_gate {t K:ℝ}(h:0<t) (hz:0≤K)(n:ℕ):
   Super (fun x=> K*(1+(radiusB x:ℝ))^n*(Real.exp (-t*radiusB x)+Real.exp (-t*Stores.till x))) := by
    intro d
    open Extra.Iteration.Scales in
     filter_upwards [(Tiny.const tendsto_id (2*K) (mul_nonneg zero_le_two hz)).mul (Tiny.cover_size.pow tendsto_id n) tendsto_id 1 zero_lt_one, tender_nat h (d+1),horizon_nat h (d+1),eventually_gt_atTop (0:ℝ)] with x hx h₁ h₂ hh
     have hW : (2*K)*(1+(radiusB x:ℝ))^n ≤ x := by simpa using! hx.2
     rw [abs_of_nonneg (by positivity)] -- omega range
     calc
      K*(1+(radiusB x:ℝ))^n*_ ≤ (2*K)*(1+(radiusB x:ℝ))^n*(x^(d+1))⁻¹:=by
          linarith only [mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (show 0 ≤K*(1+(radiusB x:ℝ))^n by positivity)]
      _ ≤ x * (x^(d+1))⁻¹:= mul_le_mul_of_nonneg_right hW (by positivity)
      _ = _:= by rw [pow_succ]; field_simp
lemma shine_gate {t N C:ℝ} (h : 0<t)(hn:0≤N)(hc:0≤C)(k:ℕ):
    Super (fun x:ℝ=> C*(1+N*(1+4*(reach x:ℝ))^k)*Real.exp (-t*(reach x:ℝ))) := by
    have hs := super_gate h (K:=(C+C*N*181^k)) (by positivity) k
    intro p
    filter_upwards [hs p] with x hx
    rw [abs_of_nonneg (by positivity)]; apply le_trans _ hx; apply le_trans _ (le_abs_self _)
    refine mul_le_mul ?_ ?_ (le_of_lt (Real.exp_pos _)) (by positivity)
    · rw [add_mul,mul_assoc (C*N),← mul_pow,mul_add C] -- pipe syntax?
      refine add_le_add ?_ ?_
      · rw [mul_one]; exact le_mul_of_one_le_right hc (one_le_pow₀ (by simp))
      · rw [← mul_assoc]; gcongr; unfold reach; push_cast; linarith
    · apply le_add_of_le_of_nonneg (Real.exp_monotone ?_) (Real.exp_pos _).le
      have hv: (radiusB x:ℝ) ≤ reach x := Nat.cast_le.mpr (show radiusB x ≤ reach x from by unfold reach; omega)
      linarith only [mul_le_mul_of_nonneg_left hv h.le]
-- fixed postal factor
lemma lease (p:ℕ) (A:ℝ) {F:ℝ→ℝ}(hF:Super F)(n q d:ℕ)(L:Side):∀ᶠ x:ℝ in atTop, (L.val:ℝ)^d*(A*(1+F x)^(n+q)*F x) ≤ (x^p)⁻¹ := by
    filter_upwards [hF (p+1),hF 0, eventually_ge_atTop ((L.val:ℝ)^d * |A| * 2^(n+q)),eventually_gt_atTop (0:ℝ)] with x hh ht hx hc
    have ht: |F x|≤ 1:=by simpa using ht
    apply le_trans (le_abs_self _); rw [abs_mul,abs_mul,abs_mul,abs_pow, abs_pow, abs_of_nonneg (by positivity : 0 ≤ (L.val:ℝ))]
    calc
     (L.val:ℝ)^d*(|A| * |1+F x|^(n+q)*|F x|) ≤ ((L.val:ℝ)^d * |A| * 2^(n+q))*(x^(p+1))⁻¹ := by
       apply le_trans _ (Eq.ge (mul_assoc ((L.val:ℝ)^d*|A|) (2^(n+q):ℝ) _)) -- try calc instead below
       rw [mul_assoc ((L.val:ℝ)^d),mul_assoc |A|]; gcongr
       exact (abs_add_le ..).trans (by rw [abs_one]; linarith)
     _ ≤ x*(x^(p+1))⁻¹:=mul_le_mul_of_nonneg_right hx (by positivity)
     _ = (x^p)⁻¹:=by rw [pow_succ]; field_simp
end YM.RG12.Spins
