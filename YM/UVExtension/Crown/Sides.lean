import YM.UVExtension.Crown.Fame
import Mathlib.Analysis.Complex.PhragmenLindelof
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Sides
open Function Set Filter Bornology Metric Complex
open scoped Classical Topology
-- all constants nonasymptotic. propagation at stage-specific capsules even if center real drifts.
variable {E:Type*}[NormedAddCommGroup E] [NormedSpace ℂ E](f:ℂ→ E)
noncomputable def berth := Ioo (-1:ℝ) 1 ×ℂ Ioo 0 1
noncomputable def green := Icc (-1:ℝ) 1 ×ℂ Icc 0 1
private lemma retains : closure berth=green:=by unfold berth; rw [closure_reProdIm,closure_Ioo (by norm_num : (-1:ℝ)≠1),closure_Ioo (by norm_num : (0:ℝ)≠1)]; rfl
private def roll (z:ℂ) := -(z^2)+4*(I*z)
private lemma rollR (z:ℂ): (roll z).re= -(z.re^2)+z.im^2-4*z.im:=by unfold roll; simp [pow_two, mul_re]; ring
variable {b M r δ θ : ℝ} (hb:0≤b)(hm:0≤M)
include hb hm
lemma pillar (hf:DifferentiableOn ℂ f green)(hp:∀ x∈ green, ‖f x‖≤ b*Real.exp M) (h:∀ i:ℝ, |i| ≤1→ ‖f i‖ ≤ b)(t:ℝ)(ht:0≤ t)(hA:t≤1): ‖f ((t:ℂ)*I)‖≤ b* Real.exp (4*t*M):=by
   let z(v:ℂ):= Complex.exp ((M:ℂ)*roll v); have hh: Differentiable ℂ z:= (((show Differentiable ℂ roll by unfold roll; fun_prop).const_mul _).cexp)
   let g (v:ℂ):= z v • f v; have he: DiffContOnCl ℂ f berth:= ⟨hf.mono (retains ▸ subset_closure),retains.symm ▸ hf.continuousOn⟩
   let w:= (t:ℂ)*I; have hg: DiffContOnCl ℂ g berth:= hh.diffContOnCl.smul he; have hz(x): ‖z x‖ = Real.exp (M*(-(x.re^2)+x.im^2-4*x.im)):=by unfold z; simp [norm_exp,rollR,Complex.mul_re]
   have hx:‖g w‖≤ b:=by
      refine norm_le_of_forall_mem_frontier_norm_le ((isBounded_Ioo ..).reProdIm (isBounded_Ioo ..)) hg ?_ ?_
      · intro v hv; have he:= frontier_subset_closure hv; change v∈closure berth at he; rw [retains] at he
        have hRe:= (mem_reProdIm.mp he).1; have hy:= (mem_reProdIm.mp he).2; by_cases h0:v.im=0
        · have hh : v=(v.re:ℂ):=Complex.ext rfl (by simp [h0]) -- semicolon
          unfold g; rw [norm_smul,hz,h0]; apply le_trans (b:=1*b) _ (one_mul ..|>.le); refine mul_le_mul (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hm (by nlinarith))) ?_ (norm_nonneg _) zero_le_one; exact (congr_arg (fun z=> ‖f z‖) hh).trans_le (h v.re (abs_le.mpr hRe))
        have hQ: -(v.re^2)+v.im^2-4*v.im ≤ -1:=by
           rw [frontier_reProdIm,frontier_Ioo (by norm_num : -(1:ℝ)<1), frontier_Ioo (by norm_num : (0:ℝ)<1)] at hv; rcases hv with hu|hu
           · have ht:v.im=1:= by have hh:=hu.2; change v.im∈({0,1}:Set ℝ) at hh; simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,h0,false_or] using hh
             rw [ht]; nlinarith
           have hh : v.re=-1∨v.re=1:= hu.1; rcases hy with ⟨hs,hA⟩; rcases hh with hh|hh <;> rw [hh] <;> nlinarith
        unfold g; rw [norm_smul,hz]; apply (mul_le_mul (show _≤Real.exp (-M) from Real.exp_monotone (by nlinarith only [mul_le_mul_of_nonneg_left hQ hm])) (hp v he) (norm_nonneg _) (Real.exp_pos _).le).trans_eq; rw [mul_left_comm (Real.exp _),← Real.exp_add]; simp
      change w ∈ closure berth; rw [retains]; change w∈ Icc _ _ ×ℂ Icc _ _; simp [w,ht,hA,mem_reProdIm]
   unfold g at hx; rw [norm_smul,hz] at hx
   have ht' : Real.exp (-(4*t*M))* ‖f w‖≤ b:= le_trans (mul_le_mul_of_nonneg_right (Real.exp_monotone (show -(4*t*M)≤ _ from (by simp only [w, mul_I_re,mul_I_im, ofReal_im, ofReal_re]; nlinarith))) (norm_nonneg _)) hx
   exact (show ‖f w‖ ≤b*Real.exp _ from (by rw [Real.exp_neg,inv_mul_eq_div] at ht'; exact (div_le_iff₀ (Real.exp_pos _)).mp ht'))

variable (hR:0<r)
-- symmetric.Y
lemma cashP (R:ℝ)(F:ℂ→ E)(hF:DifferentiableOn ℂ F (ball 0 R))(hC:0 < r)(hA:∀ z∈ball 0 R,‖F z‖≤ b* Real.exp M)(ht:∀ x:ℝ,|x|<R→‖F x‖ ≤ b)(a k:ℝ)(hk:k≠0)(ha: |a|+3*|k|< R)(i:ℝ)(hv:0≤ i)(hp:i ≤1): ‖F ((a:ℂ)+(k:ℂ)*((i:ℂ)*I))‖ ≤ b* Real.exp (4*i*M):=by
    let f(z:ℂ):=(a:ℂ)+(k:ℂ)*z; have hh:Differentiable ℂ f:= differentiable_id.const_mul _ |>.const_add _
    have he : MapsTo f green (ball 0 R):= by
       intro z hz; have h':= (mem_reProdIm.mp hz).1; have hV:= (mem_reProdIm.mp hz).2
       have hr: |z.im|≤1:= by rw [abs_of_nonneg hV.1]; exact hV.2
       apply mem_ball_zero_iff.mpr; refine lt_of_le_of_lt (norm_add_le ..) (lt_of_le_of_lt ?_ ha); rw [norm_mul,norm_real,norm_real]; apply add_le_add_right
       rw [mul_comm (3:ℝ)]; exact mul_le_mul_of_nonneg_left ((norm_le_abs_re_add_abs_im _).trans (by linarith only [abs_le.mpr h',hr])) (abs_nonneg _)
    refine pillar (b:=b) (M:=M) (F∘f) hb hm (hF.comp hh.differentiableOn he) (fun x hx=> hA _ (he hx)) ?_ i hv hp
    intro i hi; have hp':|a+k*i|<R:= (abs_add_le ..).trans_lt (by rw [abs_mul]; have h':=mul_le_of_le_one_right (abs_nonneg k) hi; linarith [abs_nonneg k]); have he:= ht (a+k*i) hp'; push_cast at he; exact he
include hR
lemma peak (hf:DifferentiableOn ℂ f (ball 0 r))(hy:∀ z∈ ball (0:ℂ) r,‖f z‖ ≤ b*Real.exp M)(ht:∀ x:ℝ,|x|<r→‖f x‖≤ b) (z:ℂ)(hh: 0<δ) (hz:|z.re|+3*δ < r) (he: |z.im|≤ δ): ‖f z‖≤ b*Real.exp (4*(|z.im|/δ)*M):=by
   have hA : |z.im|/δ ≤ 1:= by apply (div_le_one hh).mpr he
   have hC : 0 ≤ |z.im|/δ:=by positivity
   let w :ℂ:= z.re; by_cases h: 0≤ z.im
   · have hx:=cashP hb hm r f hf hR hy ht z.re δ hh.ne' (by rwa [abs_of_pos hh]) _ hC hA
     convert! hx using 3; rw [abs_of_nonneg h]; push_cast; rw [← mul_assoc, mul_div_cancel₀ _ (ofReal_ne_zero.mpr hh.ne'), Complex.re_add_im]
   have hp:=cashP hb hm r f hf hR hy ht z.re (-δ) (neg_ne_zero.mpr hh.ne') (by rwa [abs_neg,abs_of_pos hh]) _ hC hA
   convert! hp using 3; rw [abs_of_nonpos (le_of_not_ge h)]; push_cast; rw [← mul_assoc, neg_mul, neg_div, mul_neg, neg_neg, mul_div_cancel₀ _ (ofReal_ne_zero.mpr hh.ne'),Complex.re_add_im]
end YM.UVExtension.Sides
