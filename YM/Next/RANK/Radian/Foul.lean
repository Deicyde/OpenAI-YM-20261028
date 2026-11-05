import YM.Next.RANK.Radian.Differ
import YM.Next.RANK.Radian.Sinks

/-!
# Fourier analytic weight on Mist remainder

Exponential used only to construct Maxwell comparison, F need only near
KER-continuum difference including directional stencils. Supports true Fourier
period data supplied when called. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice  Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace
variable {n D : ℕ} {F G : E4→ℂ} {U : Set E4} {C c r M : ℝ}

private lemma flight (F : E4→ℂ) (n : ℕ) (h : ContDiff ℝ (↑n) F) (hp : ∀ i≤n, Integrable (iteratedFDeriv ℝ i F)) (he : ∀ i≤n,(∫ x,‖iteratedFDeriv ℝ i F x‖) ≤ C) (x : E4) :
    ‖x‖^n * ‖harmon F x‖ ≤ 2^n*((n:ℝ)+1)*C := by
  have ht : ContDiff ℝ (↑(n:ℕ∞):WithTop ℕ∞) F := h
  have hV := Real.pow_mul_norm_iteratedFDeriv_fourier_le (K:=0) ht (fun k i hk hi=> ?_) (k:=0) (n:=n) (by simp) (by simp) (-x);swap
  · have hb:k=0:=by simpa only [nonpos_iff_eq_zero, Nat.cast_eq_zero] using hk
    simpa [hb] using! (hp i (by exact_mod_cast hi)).norm
  simp only [norm_neg,norm_iteratedFDeriv_zero, pow_zero,one_mul, Nat.cast_zero,mul_zero,zero_add] at hV
  refine hV.trans ?_; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (by positivity)
  let L:=Finset.range 1 ×ˢ Finset.range (n+1)
  apply le_trans (b:=∑ _∈L,C); apply sum_le_sum; intro i hi; simp only [mem_product, Finset.mem_range] at hi; simpa only [show i.1=0 from by omega,pow_zero,one_mul] using he _ (by omega : i.2≤n)
  simp [L]
private lemma awake (F : E4→ℂ) (_ : Integrable F) (x : E4) : ‖harmon F x‖ ≤ (∫ i,‖F i‖):= by
  rw [wind]; apply (norm_integral_le_integral_norm ..).trans; simp [price_wave]
lemma indigo (n : ℕ) : ∃ L : ℝ, 0 ≤ L∧ ∀ F C (h : Mist F n C), 0≤ C → Integrable F→ ∀ z : E4,1≤‖z‖→
    ‖harmon F z‖ ≤ C*L / ‖z‖^(n+5):= by
  obtain ⟨L,hL,hP⟩:= settles n
  let D:= n+6; let E:= n+5; let p:=∫ x,reach 1 x;let W := volume.real (Metric.ball (0:E4) 1);let N :=2^D*((D:ℝ)+1)
  have hp : 0≤p := integral_nonneg (therein · 1); have hN : 0 ≤ N:= by unfold N; positivity
  have hW : 0 ≤ W := measureReal_nonneg
  refine ⟨N*L*p + W,by positivity,?_⟩; intro F C h hx hv z hz; let s:=‖z‖; let r:= s⁻¹
  have he:0<s:=zero_lt_one.trans_le hz;have hr : 0<r:= inv_pos.mpr he;have ht : r≤1:= inv_le_one_of_one_le₀ hz
  let R:=sail r * F
  have hh : ContDiff ℝ (↑D) R:= evening_smooth hr h.part
  have hs i(hi:i≤D):Integrable (iteratedFDeriv ℝ i R):= by
    refine ((reaching hr).const_mul (C*L)).mono' ((hh.continuous_iteratedFDeriv (m:=i) (by exact_mod_cast hi)).aestronglyMeasurable) (Eventually.of_forall fun i'=> hP i hi F C h hx _ hr ht _)
  have hw : ‖harmon R z‖ ≤ N*C*L*p / s^E:= by
    have hh:= flight R D hh hs (C:=C*L*p/r) ?_ z; rotate_left
    · intro i hi; apply le_trans (b:=∫ i : E4,(C*L)*reach r i)
      · exact integral_mono (hs i hi|>.norm) ((reaching hr).const_mul _) (fun _=>hP i hi F C h hx _ hr ht _)
      rw [integral_const_mul, slope hr,mul_div_assoc]
    have hz : D= E+1:= by unfold D E;omega
    change s^D*_≤ N*_ at hh
    have hq:C*L*p/r=C*L*p*s:= by unfold r; field_simp
    rw [hz,pow_succ,hq] at hh; apply (le_div_iff₀ (pow_pos he E)).2; apply le_of_mul_le_mul_right (a:=s) _ he; linarith only [hh]
  have hR : Integrable R:= by
    apply (integrable_norm_iff hh.continuous.aestronglyMeasurable).1; simpa only [norm_iteratedFDeriv_zero] using! (hs 0 (by omega)).norm
  let P:= F-R; have hv' : Integrable P:=hv.sub hR
  let t:=Metric.closedBall (0:E4) r
  have hu : ‖harmon P z‖ ≤ C*W / s^E:= by
    let g:E4→ℝ:= t.indicator (fun x=>C*r^(n+1))
    have hc : Integrable g:= (integrable_indicator_iff isClosed_closedBall.measurableSet).2 (integrableOn_const (hs:=(isCompact_closedBall (0:E4) r).measure_lt_top.ne))
    apply (awake P hv' z).trans
    apply (integral_mono_ae hv'.norm hc (lit_ae.mono fun x he'=>?_)).trans
    · rw [integral_indicator isClosed_closedBall.measurableSet (f:=fun _=>C*r^(n+1)), setIntegral_const]
      -- weight
      have he':volume.real t=r^4*W:= by
        unfold W t Measure.real; rw [Measure.addHaar_closedBall volume _ hr.le,spaceD,ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_pos hr _).le]
      rw [he']; apply le_of_eq; rw [smul_eq_mul]; unfold E r; rw [inv_pow,inv_pow, pow_add, pow_add]; field_simp
    change ‖P x‖ ≤ g x; by_cases hb:x∈t
    · have hz : ‖x‖ ≤ r := by simpa [t] using hb
      have H : P x=basin r x * F x:= by
        change F x-(1-basin r x)*F x=_
        ring
      rw [H,norm_mul,show g x=C*r^(n+1) from indicator_of_mem hb _]; apply (mul_le_of_le_one_left (norm_nonneg _) (hue r _)).trans
      have ht:= h.jet 0 (by omega) x he' (hz.trans ht);simp only [norm_iteratedFDeriv_zero, pow_zero,mul_one] at ht; exact ht.trans (by gcongr)
    have ht : r< ‖x‖:=by simpa [t] using hb
    rw [show P x=0 from sub_eq_zero.mpr (show F x= R x from (untouched hr _ ht).eq_of_nhds.symm), norm_zero,show g x=0 from indicator_of_notMem hb _]
  have he' : harmon F z= harmon P z+harmon R z:=by unfold P; rw [harmon_sub hv hR, Pi.sub_apply]; abel
  rw [he'];apply (norm_add_le ..).trans; exact (add_le_add hu hw).trans_eq (by unfold s N D E; ring)
end YM.Next.Rank.Radian
