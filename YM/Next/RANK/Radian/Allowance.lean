import YM.Bid.Loan
import YM.Next.RANK.BoundParticle
import YM.Next.RANK.Radian.Heat
import YM.Next.RANK.Radian.Nodes

/-!
# Quantitative quadrature with one pole

Assume only multiplier bound on SCALAR symbol & (weight-one) derivative. includes
values at zero amplitude reading despite integral doesn't there. Kernel use through
periodic stencil proofs. True E4 pi Lebesgue.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Radian
open MeasureTheory Measure Filter Maxwell Topology Analysis Asymptotics Set Real Metric Beamer Lattice  Finset
open scoped ContDiff Topology BigOperators Classical NNReal ENNReal FourierTransform RealInnerProductSpace

variable {V : Type*} {k : ℕ} {P : Side} {r C M b : ℝ} {F G : E4→ℂ}

lemma flits (x : E4) : Continuous (wave x) := by unfold wave; fun_prop
lemma flute (z x : E4) : DifferentiableAt ℝ (wave z) x ∧ ‖fderiv ℝ (wave z) x‖≤ 2*π*‖z‖:= by
  let L:= innerSL (E:=E4) ℝ
  let T:E4→ℂ:= fun t => (Real.fourierChar (-((L t) (-z))):Circle)
  refine ⟨?_,?_⟩
  · exact (Real.hasFDerivAt_fourierChar_neg_bilinear_left L x (-z)).differentiableAt
  change ‖fderiv ℝ T x‖≤ _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun y => ?_)
  rw [show fderiv ℝ T x y= _ from Real.fderiv_fourierChar_neg_bilinear_left_apply L x y (-z)]
  simp_rw [norm_mul, norm_neg, Complex.norm_two, Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos,Complex.norm_I,Circle.norm_coe,mul_one]
  change 2*π*|⟪y,-z⟫|≤ _; have he:= abs_real_inner_le_norm y (-z); rw [norm_neg] at he; linarith only [mul_le_mul_of_nonneg_left he (show 0 ≤ π from Real.pi_pos.le)]

lemma furl (x u z : E4): ‖wave z x-wave z u‖ ≤ 2*π*‖z‖*‖x-u‖:= by
  exact (convex_univ (𝕜:=ℝ)).norm_image_sub_le_of_norm_fderiv_le (fun w _=> (flute z w).1) (fun w _=> (flute z w).2) (Set.mem_univ u) (Set.mem_univ x)

lemma fern (x : E4) {r : ℝ} (h : 0<r) (hx : 0<‖x‖) (hp : ‖x‖≤r) :
    ‖x‖⁻¹ ≤ (Maxwell.normal⁻¹ * Real.exp (r^2)*r)* ‖liturgy 1 x‖:= by
  rw [lit_norm]; let s:= ‖x‖; have hz := Real.exp_le_exp.mpr (show -(r^2)≤ - (s^2) from neg_le_neg (pow_le_pow_left₀ hx.le hp 2)); let T:= Real.exp (-s^2);let u:=Real.exp (r^2)
  have he:1 ≤ u*T:= by
    rw [show 1=u*Real.exp (-r^2) by unfold u; rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]]; exact mul_le_mul_of_nonneg_left hz (Real.exp_pos _).le
  simp only [neg_mul,one_mul]
  change s⁻¹≤ normal⁻¹ *u*r*(normal*T/s^2)
  have hh : s ≤ u*T*r:= hp.trans (by nlinarith only [mul_le_mul_of_nonneg_right he h.le])
  have hv:=Maxwell.normal_pos; calc
    _ = s/s^2:= by field_simp
    _ ≤ _:= div_le_div_of_nonneg_right hh (sq_nonneg _)
    _ = _:= by field_simp

structure Lip (f : E4→ℂ) (p : ℕ) (C : ℝ) : Prop where
  event : eventP p f
  norm i : ‖f i‖ ≤ C
  direct i (h : i≠0) : DifferentiableAt ℝ f i
  works i (h : i ≠ 0) : ‖fderiv ℝ f i‖*‖i‖ ≤ C

lemma skin (h : Lip F k C) (he : 0 ≤ C) (x u : E4) (d : ℝ) (hd : 0<d) (hv : ‖u-x‖≤ d) (hx : x∈away) :
    ‖F x - F u‖ ≤ 4*C * ‖x‖⁻¹*d := by
  let p:= ‖x‖; have hp : 0 < p := norm_pos_iff.mpr hx
  by_cases hz: 2*d ≤ p
  · have ht v (hv : v∈ Metric.closedBall x d): p/2≤ ‖v‖ := by
      have he := sub_le_comm.mp (norm_sub_norm_le x v); rw [norm_sub_rev] at he; have hp :=Metric.mem_closedBall.mp hv; rw [dist_eq_norm] at hp; unfold p at *; linarith
    have hy v (hv : v∈ Metric.closedBall x d):0<‖v‖:=lt_of_lt_of_le (half_pos hp) (ht _ hv)
    have hb : ‖F u-F x‖ ≤ (2*C*p⁻¹)*‖u-x‖:= by
      apply Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (s:=closedBall x d)
      · exact fun i hi=> h.direct i (norm_pos_iff.mp (hy i hi))
      · intro i hi; apply le_trans _ (le_of_eq (show C/(p/2)=_ by ring))
        rw [le_div_iff₀ (by positivity)]; exact (mul_le_mul_of_nonneg_left (ht i hi) (norm_nonneg _)).trans (h.works i (norm_pos_iff.mp (hy i hi)))
      · exact convex_closedBall ..
      · exact mem_closedBall_self hd.le
      · exact Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hv)
    rw [norm_sub_rev]; apply hb.trans;change 2*C*p⁻¹*_ ≤ 4*C*p⁻¹*d; gcongr; norm_num -- gcongr
  apply (norm_sub_le ..).trans; apply (add_le_add (h.norm x) (h.norm u)).trans
  unfold p at *; field_simp
  nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hz) he]


-- need no uniform lower-size derivative scale. Require meas inherited C caps.
theorem powder (k : ℕ) : ∃ A : ℝ,0≤ A ∧ ∀ F C, 0≤C→Integrable F → Lip F k C→∀ c z,
    ‖harmon F z-scansP c (fun u=> wave z u * F u) k‖ ≤ A*C*(1+‖z‖) / c.val := by
  let W:= (k:ℝ)+ 5
  have hw:0<W:= add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (by norm_num)
  let L:=Maxwell.normal⁻¹ * Real.exp (W^2)*W
  let K:= Metric.closedBall (0:E4) W
  let J:=volume.real K
  let V:=∫ x:E4, ‖liturgy 1 x‖
  have hV : 0 ≤ V:= integral_nonneg (fun i=> norm_nonneg _); have hx : 0 ≤ J := measureReal_nonneg
  have hp : 0 ≤ L:= by have := normal_pos;unfold L;positivity
  let A:=16*L*V+8*π*J
  refine ⟨A,by unfold A; positivity,?_⟩; intro F C he hT H P z
  let s : ℝ:=(P.val:ℝ)⁻¹; have hs:0<s:= positive P; have h1:s≤1:= inv_le_one_of_one_le₀ (by exact_mod_cast P.property)
  let B x := wave z x * F x; let N v:= addr P (mark P v)
  obtain ⟨hd,hz⟩:=grid_born P B k (fun i hi=> by unfold B; rw [H.event i hi,mul_zero]); have hb : Integrable B:= hT.bdd_mul ((flits z).aestronglyMeasurable) (Eventually.of_forall (p:=fun i=> ‖wave z i‖≤1) (by simp))
  let f (i : E4):= K.indicator (fun _=>8*π*C*‖z‖ * s) i; let v(x : E4):= (L*(16*C)*s) * ‖liturgy 1 x‖
  have hh : Integrable v:= (liturgy_int (b:=1) (by norm_num)).norm.const_mul _
  have hf : Integrable f:= (integrable_indicator_iff isClosed_closedBall.measurableSet).2 <| integrableOn_const (hs:=(isCompact_closedBall _ _).measure_lt_top.ne) -- extra
  rw [wind,← hz,← integral_sub hb hd]; apply (norm_integral_le_integral_norm ..).trans
  refine (integral_mono_ae (hb.sub hd|>.norm) (hh.add hf) (lit_ae.mono fun x h=>?_)).trans ?_; swap
  · have ht:(∫ x,(v+f) x)=(L*(16*C)*s)*V+J*(8*π*C*‖z‖*s):= by simp only [Pi.add_apply];rw [integral_add hh hf]; unfold v f; rw [integral_indicator isClosed_closedBall.measurableSet, setIntegral_const,integral_const_mul]; rfl
    refine ht.le.trans ?_; rw [div_eq_mul_inv]; unfold A; change _ ≤ _*s; linarith only [show 0≤ L*V*‖z‖*C*s by positivity,show 0 ≤ π*J*C*s by positivity]
  change ‖B x-B (N x)‖ ≤ v x+f x; have ht: ‖N x-x‖ ≤4*s:= by have hh:=rock (c:=P) x; rwa [dist_eq_norm] at hh
  by_cases hg:x∈K
  · have hp := norm_pos_iff.mpr h; have hu : ‖x‖≤W:= by simpa only [K,mem_closedBall,dist_zero_right] using hg
    have hE:‖F x-F (N x)‖ ≤v x:= by
      apply (skin H he x _ _ (by positivity) ht h).trans; unfold v; linarith only [mul_le_mul_of_nonneg_right (fern _ hw hp hu) (show 0 ≤ C*s by positivity)]
    have hu: B x-B (N x)= wave z (N x)*(F x - F (N x))+(wave z x-wave z (N x))*F x:= by unfold B;ring
    rw [hu];apply (norm_add_le ..).trans;rw [norm_mul,norm_mul,price_wave,one_mul];apply add_le_add hE; rw [show f x=(8*π*C*‖z‖*s) from indicator_of_mem hg _]; apply (mul_le_mul (le_trans (furl x (N x) z) ?_) (H.norm x) (norm_nonneg _) (b:=2*π*‖z‖*(4*s)) (by positivity)).trans (le_of_eq (by ring)); rw [norm_sub_rev]; gcongr
  have hz:W<‖x‖:=by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hg
  have hP: (k:ℝ)<‖N x‖:= by have hi:=norm_sub_norm_le x (N x);rw [norm_sub_rev] at hi; unfold W at *; linarith only [hi,hz,h1,ht]
  rw [show f x=0 from indicator_of_notMem hg _,add_zero]; unfold B; rw [H.event x (by unfold W at *;linarith only [hz]),H.event _ hP,mul_zero,mul_zero,sub_zero,norm_zero]; unfold v; positivity
end YM.Next.Rank.Radian
