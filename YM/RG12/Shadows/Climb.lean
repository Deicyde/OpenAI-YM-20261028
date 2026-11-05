import YM.RG12.Shadows.Display
import YM.Work.C05
/-! No analytic remainder charge if applied at the center.
Kernel buys exp Δ with quadratic suppression in value and all through n. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function ConnectedActivityE6 ConnectedActivityE6.Blaze
open scoped ContDiff Topology BigOperators Classical
variable {R:Haze}{n:ℕ}{p t :ℝ}{s q : Bool}{I I' J:ℕ→Type}{E:ℕ→Type} [∀ i,NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
namespace Call
variable {f:Drift I E}(h: Call R n 0 f)
abbrev Marks (f:Drift I E)(r:ℝ):=∀ᶠ i:ℕ in atTop,∀ j,|f i j (0:E i)| ≤ r
include h
lemma lifts (g:ℝ→ℝ)(hg:ContDiff ℝ n g){r:ℝ}(hr: Marks f r):Call R n 0 (fun i k=> g∘ f i k):=by
  obtain ⟨C,hC,hX⟩:=Brush.compact (k:=n) (f:=g) (s:=Icc (-r) r) isCompact_Icc (fun x _=> hg.contDiffAt)
  obtain ⟨v,hv,he⟩:=h
  refine ⟨fun i=> (n.factorial*C) * (1+(1+v i))^n,?_ ,?_⟩
  · refine Charges.left ?_ _; exact (((Charges.frozen 1 R).add ((Charges.frozen 1 R).add hv)).raise n rfl)
  filter_upwards [he,hr] with i ha hp j; simpa only [mul_one] using! ((ha j).pine (hX _ (abs_le.mp (hp j)))).trim
omit h
lemma marks {f:Drift I E}(H:Call R n p f)(hP:0<p):Marks f 1:=by
   obtain ⟨v,ha,hb⟩:= H; filter_upwards [hb,(ha.tend0 hP).eventually (ge_mem_nhds zero_lt_one)] with i hb ht j using ((hb j).bound.trans ht)
lemma expD {f:Drift I E}(H:Call R n p f)(hP:0<p):Call R n p (fun i j y=>Real.exp (f i j y)-1):=by
   obtain ⟨v,ha,hb⟩:=H; obtain ⟨C,hC,hX⟩:=Brush.expands n; refine ⟨_,ha.left C,?_⟩
   filter_upwards [hb,(ha.tend0 hP).eventually (ge_mem_nhds zero_lt_one)] with i hb ht j using hX _ _ _ _ _ (hb j) ht
-- exploit Complex.dslope
private lemma analytical : ∃ f:ℝ→ℝ, ContDiff ℝ ∞ f ∧ ∀ x, Real.exp x-1-x=x*x*f x:=by
   let B:= dslope Complex.exp (0:ℂ)
   let D:= dslope B (0:ℂ)
   have H : Differentiable ℂ B:=by rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]; exact Complex.differentiable_exp.differentiableOn
   have hD : Differentiable ℂ D:=by rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]; exact H.differentiableOn
   refine ⟨Complex.reCLM ∘ D ∘ Complex.ofRealCLM,Complex.reCLM.contDiff.comp ((hD.contDiff.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff),?_⟩
   intro x
   have hc : ∀ x:ℂ, Complex.exp x-1-x=x*(x*D x):=by
      intro x; have h:=sub_smul_dslope Complex.exp 0 x; have hy:=sub_smul_dslope B 0 x
      change (x-0)*B x=_ at h; rw [sub_zero,Complex.exp_zero] at h; change (x-0)*D x=B x-B 0 at hy
      rw [sub_zero,show B 0=1 by simp only [B,dslope_same,(Complex.hasDerivAt_exp 0).deriv,Complex.exp_zero]] at hy; rw [hy,mul_sub,mul_one,h]
   have he:= congr_arg Complex.re (hc x); rw [←Complex.ofReal_exp] at he; simpa only [Function.comp_apply,Complex.reCLM_apply,Complex.ofRealCLM_apply,Complex.sub_re,Complex.ofReal_re, Complex.one_re,Complex.mul_re,Complex.ofReal_im,zero_mul,sub_zero,mul_assoc] using he
lemma expRD {f:Drift I E}(H: Call R n p f)(hP:0<p):Call R n (p+p) (fun i j y=> Real.exp (f i j y)-1-f i j y):=by
   obtain ⟨B,hC,hX⟩:= analytical
   have hf:= (H.times H).times ((H.mono hP.le).lifts B (hC.of_le (WithTop.coe_le_coe.mpr le_top)) (H.marks hP)); rw [add_zero] at hf
   exact hf.same (fun i j x=> hX _)
end Call
namespace Touch
open Call
variable {f g:Drift I E}
lemma exp (h: Touch R n 0 true f g){r:ℝ}(hp:Marks f r)(hq:Marks g r) : Touch R n 0 true (fun i j y=> Real.exp (f i j y)) (fun i j y=>Real.exp (g i j y)):=by
  let F:Drift I E:= fun i j y=>Real.exp (f i j y)
  let G: Drift I E:= fun i j y=>Real.exp (g i j y)
  have he:= h.origin.lifts _ Real.contDiff_exp hp; have hy : Call R n 0 G:= h.remote.lifts _ Real.contDiff_exp hq
  have hf:Call R n 1 (f-g):= by simpa only [zero_add,aura,one_smul] using h.listens
  refine ⟨he,?_⟩; rw [zero_add]
  have hx:= (hf.expD zero_lt_one).times hy; rw [add_zero] at hx; exact hx.same (fun i j x=> by
     simp only [Pi.sub_apply,Pi.mul_apply, G, aura,one_smul,sub_mul,one_mul,←Real.exp_add,sub_add_cancel])
lemma expComp (h:Touch R n 1 false f g): Touch R n 1 false (fun i j y=> Real.exp (f i j y)-1) (fun i j y=>Real.exp (g i j y)-1):=by
   let F {i}:=(fun (j:I i) y=>Real.exp (f i j y)-1)
   let G {i}:=(fun (j:I i) y=>Real.exp (g i j y)-1)
   have h0:=h.origin.expD zero_lt_one
   have h1:=h.origin.expRD zero_lt_one
   have h2:=h.remote.expRD zero_lt_one
   refine ⟨h0,?_⟩
   exact ((h.listens.adds h1).adds h2).same (fun _ _ _=> by simp only [Pi.sub_apply, Pi.neg_apply, Pi.add_apply, aura,neg_smul,one_smul]; abel)
end Touch
namespace Tilts
open Call
variable {f h g k:Drift I E}
lemma exp (U:Tilts R n 0 true f h g k){r:ℝ}(hf:Marks f r)(hh:Marks h r):Tilts R n 0 true (fun i j y=>Real.exp (f i j y)) (fun i j y=>Real.exp (h i j y)) (fun i j y=>Real.exp (g i j y)) (fun i j y=>Real.exp (k i j y)):=by
   have H:= U.beam.exp hf hh
   refine ⟨H,?_⟩
   have hv:= U.shade; change Touch _ _ _ false _ _ at hv; rw [zero_add] at hv ⊢
   have h:= hv.expComp.times H; rw [add_zero] at h
   exact h.same (fun _ _ _=> by simp only [Pi.sub_apply,Pi.mul_apply,sub_mul,one_mul,←Real.exp_add,sub_add_cancel]) (fun _ _ _=> by simp only [Pi.sub_apply,Pi.mul_apply,sub_mul,one_mul,←Real.exp_add,sub_add_cancel])
end Tilts
end YM.RG12.Shadows
