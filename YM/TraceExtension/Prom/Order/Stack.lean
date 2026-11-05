import YM.TraceExtension.Prom.Order.Kiss
import YM.TraceExtension.Prom.Front.West.Lys
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function Filter MeasureTheory Finset Lattice Wilson RG Precision
open Pressure Push.SectorMeasure Next.Rank RankCovariance Thirst  Ac Baler Glyph Tapes Marker
open Display Display.Docking  Value Flux SectorNext.Vacuum Station Perch
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
lemma raises_more (L R b : ℝ) (hL:1<L)(hR:1<R)(hb:0≤b) : ∃ a:ℝ,0≤a ∧ ∀ᶠ s:ℝ in atTop, stretch L b s ≤ stretch R a s:=by
    let x:=Real.log L;let y:=Real.log R; have hx:0<x:=Real.log_pos hL;have hy:0<y:=Real.log_pos hR
    let a:= y*( (b+3)/x+2);have ha :0 ≤ a:= by unfold a; positivity
    refine ⟨a,ha,?_⟩
    filter_upwards [Perch.boil_rate.eventually_ge_atTop 1,Perch.many.eventually_ge_atTop 1,Perch.rate_wall zero_lt_one 5] with s hs hv hr
    let V (p:ℝ):=bump L p s;let f:=boil s;change 1≤ f at hs; have hf : 0≤f:= hs.trans' zero_le_one
    have hg (p:ℝ): Real.log ((YM.Vac.Numbers.P s)^p*(YM.Vac.Numbers.P s)^2)=(p+2)*f:= by unfold YM.Vac.Numbers.P; rw [Real.log_mul (by positivity) (by positivity),Real.log_rpow (Real.exp_pos _),Real.log_pow,Real.log_exp];push_cast;unfold f boil Perch.y; ring
    have hm : (V b:ℝ) ≤ (b+2)*f/x+1:= by unfold V bump want; rw [hg]; exact (Nat.ceil_lt_add_one (show 0 ≤ (b+2)*f/x by positivity)).le
    have hM: 1 ≤ (M s:ℝ):= by exact_mod_cast hv
    have hV : Real.log ((M s:ℝ)^10) ≤f := by
       unfold walls at hr; rw [Nat.cast_pow,Real.log_pow,Nat.cast_ofNat] at hr
       rw [Real.log_pow, Nat.cast_ofNat]; linarith only [hr]
    have hx' : (more L s:ℝ) ≤ f/x+1:= by
       have hz: 0≤ Real.log ((M s:ℝ)^10):= Real.log_nonneg (one_le_pow₀ hM)
       exact (Nat.ceil_lt_add_one (div_nonneg hz hx.le)).le.trans (add_le_add_left (div_le_div_of_nonneg_right hV hx.le) _)
    have hv': ((a+2)*f/y) ≤ (bump R a s:ℝ):= by unfold bump want;rw[hg];apply Nat.le_ceil
    apply le_trans _ (Nat.le_add_right (bump R a s) (more R s))
    apply (Nat.cast_le (α:=ℝ)).mp; unfold stretch; push_cast
    apply (add_le_add hm hx').trans (le_trans _ hv'); apply (le_div_iff₀ hy).mpr
    have h : ( (b+2)*f/x+f/x+2*f)*y=a*f:= by unfold a; field_simp; ring
    linarith only [h,hs,hf,mul_le_mul_of_nonneg_right hs hy.le]
lemma bump_s (b d:ℝ)(h:b ≤ d)(L:ℝ)(hl:1<L)(s:ℝ) : bump L b s ≤ bump L d s:=by
    let x:=YM.Vac.Numbers.P s; have hx : 1 ≤ x:=Real.one_le_exp (sq_nonneg _); have hg : 0 < x:=zero_lt_one.trans_le hx
    apply Nat.ceil_le_ceil; apply div_le_div_of_nonneg_right _ (Real.log_pos hl).le
    apply Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hg _) (pow_pos hg _)); exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx h) (pow_nonneg hg.le _)
lemma rate_bump {L s t b:ℝ}(h:Real.exp 1 ≤ s)(hs:s ≤ t)(hp:1<L)(hb:0 ≤ b) : stretch L b s ≤ stretch L b t:=by
    have hr:1 ≤ s:= le_trans (Real.one_le_exp (by norm_num)) h; have hv:0<s:=zero_lt_one.trans_le hr
    have hz:= (Real.log_le_log hv hs); have hx: 1 ≤ Real.log s:= by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) h
    have h₂:=Real.log_le_log (zero_lt_one.trans_le hx) hz; have hff: Vac.Numbers.P s ≤ Vac.Numbers.P t:= Real.exp_le_exp.mpr (pow_le_pow_left₀ (Real.log_nonneg hx) h₂ _)
    apply Nat.add_le_add
    · unfold bump want; apply Nat.ceil_le_ceil;apply div_le_div_of_nonneg_right _ (Real.log_pos hp).le; refine Real.log_le_log ?_ ?_
      · have ht:=Real.exp_pos ((Real.log (Real.log s))^2); apply mul_pos (Real.rpow_pos_of_pos ht _) (pow_pos ht _)
      have ht:0 ≤ Vac.Numbers.P s:= (Real.exp_pos _).le; exact mul_le_mul (Real.rpow_le_rpow ht hff hb) (pow_le_pow_left₀ ht hff _) (pow_nonneg ht _) (Real.rpow_nonneg (ht.trans hff) _)
    unfold more want; apply Nat.ceil_le_ceil;apply div_le_div_of_nonneg_right _ (Real.log_pos hp).le; refine Real.log_le_log ?_ ?_
    · apply pow_pos; apply Nat.cast_pos.mpr; apply Nat.ceil_pos.mpr; exact pow_pos (zero_lt_one.trans_le hx) _
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.ceil_le_ceil (pow_le_pow_left₀ (zero_le_one.trans hx) hz _))) _
end YM.PhysicalNext.InteractingRank.Soft
