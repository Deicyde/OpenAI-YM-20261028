import YM.UVExtension.Lamppost.Capsule
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.Algebra.Polynomial

/-! Finite real sampling on a narrow chassis fed by Cauchy on wider.
    No analyticity of neighborhood of G payload itself; one scalar Meter read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Lamppost
open Function Filter Set Complex MeasureTheory Topology Metric Polynomial
open scoped ContDiff BigOperators NNReal ENNReal Interval Classical
variable {R b r u v : ℝ} {f : ℂ→ℂ} {S : Set ℂ}

lemma sinP (N : ℕ) (hu: 0 ≤ u) (hp:0≤b) (h:b < R) (he : DifferentiableOn ℂ f (closedBall 0 R))(hk:∀ z:ℂ, ‖z‖≤ R→‖f z‖ ≤ u): ∃ g: Polynomial ℂ, g.degree < (N:WithBot ℕ) ∧ ∀ z:ℂ, ‖z‖ ≤ b→ ‖f z-g.eval z‖≤ u*(b/R)^N*(1-b/R)⁻¹ := by
  let p:= cauchyPowerSeries f 0 R; let t:ℕ→ℂ := fun n=> p n fun _=> (1:ℂ)
  let a (n:ℕ) (z:ℂ):=p n fun _=> z
  have ht(n)(z):a n z=t n*z^n:=by unfold a t p cauchyPowerSeries; simp; ring
  let g:=∑ i:Fin N, Polynomial.C (t i)*Polynomial.X^i.val
  refine ⟨g, degree_sum_fin_lt _,fun z hz=>?_⟩
  have hr:0<R:= hp.trans_lt h
  let R': ℝ≥0 := ⟨R,hr.le⟩
  have he':HasSum (fun n:ℕ=> a n z) (f z) := by
    have he := he.hasFPowerSeriesOnBall (R:=R') (show 0<R' from hr)
    have hv:= he.hasSum (y:=z) ?_
    swap
    · rw [Metric.eball_coe]; exact mem_ball_zero_iff.mpr (hz.trans_lt h)
    rwa [zero_add] at hv
  let d(n:ℕ):= a n z
  let q:= b/R; have hq:0≤q:=div_nonneg hp hr.le; have hi:q < 1:= (div_lt_one hr).2 h
  have hZ n : ‖d n‖ ≤ u*q^n:= by
    apply (show ‖d n‖≤ ‖p n‖* ∏ _i:Fin n, ‖z‖ from (p n).le_opNorm (fun _=>z))|>.trans
    have hg:ContinuousOn (fun x:ℝ=> ‖f (_root_.circleMap 0 R x)‖) (Icc 0 (2*Real.pi)):= ((he.continuousOn.comp (continuous_circleMap ..).continuousOn (fun x _=> sphere_subset_closedBall (circleMap_mem_sphere _ hr.le _))).norm)
    have hh := norm_cauchyPowerSeries_le f 0 R n
    have hposit:= Real.two_pi_pos
    let r:=2*Real.pi
    have hx:(2*Real.pi)⁻¹*(∫ θ:ℝ in 0..2*Real.pi, ‖f (_root_.circleMap 0 R θ)‖)≤u:= by
      have h:= intervalIntegral.integral_mono_on (μ:=volume) hposit.le (hg.intervalIntegrable_of_Icc hposit.le) intervalIntegrable_const (g:=fun _=>u) (fun i hi=>hk _ (mem_closedBall_zero_iff.mp (sphere_subset_closedBall (circleMap_mem_sphere (0:ℂ) hr.le i))))
      rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at h; exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hposit.le)).trans_eq (inv_mul_cancel_left₀ hposit.ne' _)
    rw [abs_of_pos hr] at hh; have hQ:= hh.trans (mul_le_mul_of_nonneg_right hx (by positivity : 0 ≤ R⁻¹^n))
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (mul_le_mul hQ (pow_le_pow_left₀ (norm_nonneg _) hz _) (pow_nonneg (norm_nonneg _) _) (by positivity)).trans_eq (by unfold q; rw [mul_assoc,← mul_pow,mul_comm _ b, div_eq_mul_inv])
  have hn(y:ℂ):g.eval y=∑ i:Fin N, a i.val y:= by simp [g,eval_finsetSum, ht]
  have hf : ∑ i∈ Finset.range N,d i+ ∑' i:ℕ,d (i+N)= f z:= (he'.summable.sum_add_tsum_nat_add (f:=d) N).trans he'.tsum_eq
  rw [hn,Fin.sum_univ_eq_sum_range (fun i=> a i z), ← hf]
  change ‖_+_-(∑ i∈Finset.range N,d i)‖ ≤ _; rw [add_sub_cancel_left]
  have hv:= (summable_geometric_of_lt_one hq hi).mul_left (u*q^N)
  have he i: ‖d (i+N)‖≤ u*q^N*q^i:=(hZ _).trans_eq (by rw [add_comm,pow_add]; ring)
  have ha : Summable (fun i=>‖d (i+N)‖):= hv.of_nonneg_of_le (fun i=> norm_nonneg _) he
  exact (norm_tsum_le_tsum_norm ha).trans ((ha.tsum_le_tsum he hv).trans_eq (by rw [tsum_mul_left,tsum_geometric_of_lt_one hq hi]))
lemma fundsP (N:ℕ) (hx:0<r) (hv:r≤ v) : ∃ a: Fin N → ℝ, (∀ i:Fin N,|a i| < r) ∧ ∃ E:ℝ,0 ≤ E∧
    ∀ (t : Polynomial ℂ),t.degree < (N:WithBot ℕ)→∀ w:ℝ,0≤w → (∀ i, ‖t.eval ↑(a i)‖≤w)→∀ z:ℂ,‖z‖ ≤ v→ ‖t.eval z‖ ≤ E*w:=by
  let a(i:Fin N):= (i.val:ℝ)/(N+1) * r
  have he i: |a i| <r:= by
    unfold a; rw [abs_of_nonneg (by positivity : 0≤ _*r)]
    have h:(i.val:ℝ) < N+1:= by exact_mod_cast i.isLt.trans (Nat.lt_succ_self _)
    exact mul_lt_of_lt_one_left hx ((div_lt_one (by positivity : (0:ℝ)<N+1)).2 h)
  let k(i:Fin N):=(a i:ℂ)
  have hk : Set.InjOn k ↑(Finset.univ : Finset (Fin N)):= by
    refine Function.Injective.injOn (fun i j h=> ?_)
    have hg:= mul_right_cancel₀ hx.ne' (Complex.ofReal_injective h); unfold a at *; let x:ℝ:= N; have hx':(i.val:ℝ)=j.val:= by field_simp at hg; exact hg
    exact Fin.ext (by exact_mod_cast hx')
  let K:= closedBall (0:ℂ) v
  let l(i: Fin N):= Lagrange.basis Finset.univ k i
  have hM(i:Fin N):∃ b:ℝ,∀ x∈ K, ‖(l i).eval x‖ ≤ b:=by obtain ⟨w,hw⟩:= (isCompact_closedBall (0:ℂ) v|>.image_of_continuousOn (l i|>.continuous.norm.continuousOn)).bddAbove; exact ⟨w,fun _ ht=> hw (mem_image_of_mem (fun x=> ‖(l i).eval x‖) ht)⟩
  choose b hB using hM
  have hq : 0 ≤ v:= hx.le.trans hv
  let W:= ∑ i, b i; refine ⟨a,he,W,Finset.sum_nonneg (fun i hi=> (norm_nonneg _).trans (hB i 0 (mem_closedBall_self hq))),fun t ht w h h' z hz=>?_⟩
  have hp: t.degree < ↑(Finset.univ : Finset (Fin N)).card:=by simpa
  nth_rw 1 [Lagrange.eq_interpolate hk hp]
  rw [Lagrange.interpolate_apply,eval_finsetSum]; refine (norm_sum_le ..).trans ?_
  unfold W; rw [Finset.sum_mul]; apply Finset.sum_le_sum; intro i _; rw [eval_mul,eval_C,norm_mul]; exact (mul_le_mul (h' i) (hB i _ (mem_closedBall_zero_iff.mpr hz)) (norm_nonneg _) h).trans_eq (mul_comm ..)

lemma rations (N:ℕ) (hx:0<r)(hv:r≤v): ∃ K:ℝ,1≤K∧∀ (f:ℂ→ℂ)(U R w:ℝ), 0 ≤ U → 0≤ w→ v < R → DifferentiableOn ℂ f (Metric.closedBall 0 R) → (∀ z:ℂ, ‖z‖≤R→ ‖f z‖≤U) → (∀ x:ℝ, |x|<r→ ‖f (x:ℂ)‖≤ w)→ U*(v/R)^N*(1-v/R)⁻¹≤ w→∀ z:ℂ, ‖z‖ ≤v → ‖f z‖≤ K*w:=by
  obtain ⟨a,h,E,hE,hQ⟩:= fundsP N hx hv
  refine ⟨1+2*E,le_add_of_nonneg_right (by positivity),fun f U R w hU hW hR hf ht hh hr z hz =>?_⟩
  obtain ⟨g,hg,hK⟩:=sinP N hU (hx.le.trans hv) hR hf ht
  have he (i):‖g.eval (a i:ℂ)‖≤w+w:=by
    refine (norm_le_norm_add_norm_sub _ _).trans (add_le_add (hh (a i) (h i)) ?_)
    apply (hK _ _).trans hr; exact (Complex.norm_real _).trans_le ((h i|>.le).trans hv)
  have hk : ‖g.eval z - f z‖ ≤ w:=(norm_sub_rev ..).trans_le ((hK z hz).trans hr)
  exact ((norm_le_norm_add_norm_sub _ _).trans (add_le_add (hQ g hg (w+w) (add_nonneg hW hW) he z hz) hk)).trans_eq (by ring)
end YM.UVExtension.Lamppost
