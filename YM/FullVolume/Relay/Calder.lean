import YM.FullVolume.Relay.Pact
import YM.FullVolume.Spiral.Chrome
import Mathlib.Analysis.Normed.Module.HahnBanach
/-! Analysis at the stop: analytic functional calculus and integration API.
 use integrals only ON measurable/integrable witnesses; extend integral from
 this subspace to all-Config sup.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac GridApprox.Nil
open PhysicalNext.Repeat PhysicalNext.Repeat.Luna.Aank Paint Tower Amp Beam MeasureTheory
variable {a b u v:ℝ}{X:Type}
namespace Feel
lemma powder {f:sun→X→ℂ}(h:Feel f v) (n:ℕ):Feel (fun s x=> f s x ^ n) (v^n):=by
    induction n with
    | zero=> simp_rw [pow_zero]; exact Feel.staticC (fun _=>1) zero_le_one (fun _=>norm_one.le)
    | succ n ih=> simp_rw [pow_succ]; exact ih.times h
lemma exponent_c {f:sun→X→ℂ}(h:Feel f v): Feel (fun s x=> Complex.exp (f s x)) (Real.exp v):=by
    have he(n:ℕ): Feel (fun (s:sun) (x:X)=> f s x ^ n/(n.factorial:ℂ)) (v^n/(n.factorial:ℝ)):=by
       have hp:((n.factorial:ℝ))⁻¹≥0:=by positivity
       have hh:= (Feel.powder h n).scales ((n.factorial:ℝ))⁻¹; rw [abs_of_nonneg hp] at hh; convert hh using 1; · ext s x; rw [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_natCast]; ring
       rw [div_eq_inv_mul]
    have hp: HasSum (fun n:ℕ=> v^n/(n.factorial:ℝ)) (Real.exp v):=by rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
    have hS:=Feel.rollup _ he hp.summable; rw [hp.tsum_eq] at hS
    simp_rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]; exact hS
lemma ofs {f:sun→ X→ ℝ}(h:Feel f a): Feel (fun s x=>(↑(f s x):ℂ)) a:=by
    have ht:= h.transit Complex.ofRealCLM (id (α:=X)) (fun z=> (Complex.norm_real z).le.trans (le_of_eq (one_mul _).symm)) zero_le_one
    rw [one_mul] at ht;exact ht
lemma real {f:sun→X→ℂ}(h:Feel f a): Feel (fun s x=>(f s x).re) a:=by
    have ht:= h.transit Complex.reCLM (id (α:=X)) (fun z=> (Complex.abs_re_le_norm z).trans_eq (one_mul _).symm) zero_le_one; rw [one_mul] at ht; exact ht
lemma negR {f:sun→X→ℝ}(h:Feel f a) : Feel (fun s x=> -f s x) a:= by simpa only [abs_neg, abs_one,one_mul,neg_smul,one_smul] using! Feel.scales h (-1)
lemma of_scalar {f:sun→ℝ}(h: PaidBeam f a): Feel (fun s (_:X)=> f s) a:=by
    have ht:= PaidBeam.transit Complex.ofRealCLM (map_sub _) zero_le_one (fun z=> (Complex.norm_real z).le.trans (le_of_eq (one_mul _).symm)) f h; rw [one_mul] at ht; exact Feel.real (Treasure.foraged ht)
lemma timesR {f g:sun→ X→ℝ}(h:Feel f a)(hp:Feel g b): Feel (fun s x=> f s x*g s x) (a*b):=by
    have hz:= Feel.times h.ofs hp.ofs|>.real; simp_rw [Pi.mul_apply,← Complex.ofReal_mul,Complex.ofReal_re] at hz; exact hz
section int
variable [MeasurableSpace X](μ:Measure X)[IsProbabilityMeasure μ]
set_option quotPrecheck false
local notation "Z"=> ↥(lp (fun _ : X=>ℂ) ⊤)
-- extensions of functional. Existence.Run.Logs.V uses false shape? no. All stamps bounded.
lemma hahnInt : ∃ L:Tint ℂ X→L[ℝ] ℂ, (∀ x, ‖L x‖ ≤ 1*‖x‖) ∧ ∀ z:Tint ℂ X,Integrable (fun y=> Tint.see ℂ y z) μ → L z=∫ y,Tint.see ℂ y z∂μ:=by
    let f(x:Z):=fun y=> x y
    let P : Submodule ℂ (lp (fun _:X=>ℂ) ⊤):= {
        carrier:={x| Integrable (fun y=> x y) μ}
        zero_mem':=integrable_const _
        add_mem':=fun {x y} h hp=> (show Integrable (f x) μ from h).add (show Integrable (f y) μ from hp)
        smul_mem':=fun i f h=> (show Integrable (fun y=> f y) μ from h).smul i }
    let Q : P →ₗ[ℂ] ℂ := {
                              toFun:=fun x=> ∫ y,x.val y ∂μ
                              map_add':=fun x y=> integral_add (show Integrable _ μ from (show Integrable (fun y=> x.val y) μ from x.property)) (show Integrable _ μ from (show Integrable (fun i=>y.val i) μ from y.property))
                              map_smul':=fun x y=> integral_smul x (f y.val) }
    have he (x:P): ‖Q x‖≤1*‖x‖:=by
        rw [one_mul]; refine le_trans (norm_integral_le_integral_norm (f x.val)) ?_; apply le_trans (b:=∫ _ : X,‖x‖ ∂μ) (integral_mono ((show Integrable (f x.val) μ from x.property).norm) (integrable_const _) (fun i=> lp.norm_apply_le_norm (by simp) _ _)) (le_of_eq ?_); simp
    let A:= Q.mkContinuous 1 he; obtain ⟨L,hL,hx⟩:= exists_extension_norm_eq (𝕜:=ℂ) P A
    refine ⟨L.restrictScalars ℝ, fun x=>?_ ,fun z hz=> hL (⟨Tint.cast z,hz⟩:P)⟩
    exact L.le_of_opNorm_le (hx.trans_le (ContinuousLinearMap.opNorm_le_bound _ zero_le_one he)) _
lemma integrating {f:sun→X→ℂ}(h:Feel f a)(hv:∀ s, Integrable (f s) μ): PaidBeam (fun s=>∫ y, f s y∂μ) a:=by
    obtain ⟨L,hL,hx⟩:= hahnInt μ; obtain ⟨u,hu,hB⟩:=h.costs
    have ht:= PaidBeam.transit L (map_sub _) zero_le_one hL u hB; rw [one_mul] at ht
    apply ht.stamp; intro i; symm; rw [hx]; simp_rw [hu]; simp_rw [hu]; exact hv i -- rw first simp_rw might no progress
end int
end Feel
section reciprocals
open Jams
variable {f g:sun→ℂ}
lemma bilimer (h:PaidBeam f a)(hp:PaidBeam g b): PaidBeam (fun i=>f i*g i) (a*b):=by
    obtain ⟨P,hP,hq⟩:= h.arrives; obtain ⟨Q,hQ,hV⟩:=hp.arrives
    let T:= ContinuousLinearMap.mul ℝ ℂ; refine ⟨brave T P Q, (braveN ..).trans ((mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ContinuousLinearMap.opNorm_mul_le ..)).trans (mul_le_mul hP hQ (norm_nonneg _) h.price)),fun i=>?_⟩
    rw [harp,hq,hV];rfl
lemma bilimerR {f g:sun→ℝ} (h:PaidBeam f a)(hp:PaidBeam g b): PaidBeam (fun i=>f i*g i) (a*b):=by
    obtain ⟨P,hP,hq⟩:= h.arrives; obtain ⟨Q,hQ,hV⟩:=hp.arrives
    let T:= ContinuousLinearMap.mul ℝ ℝ; refine ⟨brave T P Q, (braveN ..).trans ((mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ContinuousLinearMap.opNorm_mul_le ..)).trans (mul_le_mul hP hQ (norm_nonneg _) h.price)),fun i=>?_⟩
    rw [harp,hq,hV];rfl
-- Plan cut to little radius chosen from budgets only.
lemma little {x:ℝ}(hx:x∈sun)(h: PaidBeam f a): PaidBeam (fun y:sun=> f (Muse.slash x hx y)- f (Jams.tip)) (|x| *a):=by
    obtain ⟨b,hb,hB⟩:=h.arrives
    let g(i:ℕ):=if i=0 then 0 else x^i • b i
    have hu (i):‖g i‖≤ |x| *‖b i‖:=by
        unfold g; split; next=> rw [norm_zero]; positivity
        next h=> rw [norm_smul,norm_pow]; exact mul_le_mul_of_nonneg_right (pow_le_of_le_one (abs_nonneg x) (abs_le.mpr hx) h) (norm_nonneg _) -- lemma
    have hp:= (paid b|>.summable).mul_left |x|; have he:= hp.of_nonneg_of_le (fun i=>norm_nonneg _) hu
    let B: Beam ℂ:= ⟨g,memℓp_gen (by simpa using he)⟩
    refine ⟨B,(paid B|>.tsum_eq.symm).trans_le ((he.tsum_le_tsum hu hp).trans ?_),fun s=>?_⟩
    · rw [tsum_mul_left,(paid b|>.tsum_eq)]; exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    rw [hB,hB]
    have h₁:= b.spar (abs_le.mpr (Muse.slash x hx s|>.property)); have h₂:= b.spar (abs_le.mpr Jams.tip.property)
    have hh:= h₁.sub h₂
    refine hh.unique ((B.spar (abs_le.mpr s.property)).congr_fun (fun i=>?_)); change (s.val*x)^i • b i-(0:ℝ)^i • b i= s.val^i • g i
    unfold g; split; next hi=>rw [hi]; simp
    next hi=>simp only [smul_smul,mul_pow,zero_pow hi,zero_smul,sub_zero]
-- requires all s bounds anyway.MADE.
lemma inverse_budget {x:ℝ}(hx:x∈sun) (h : PaidBeam f a) {c:ℝ} (hc:0<c)(ht:∀ s:sun,c ≤ ‖f s‖)(hp:|x| *a*c⁻¹ ≤ 1/2): PaidBeam (fun i : sun=> (f (Muse.slash x hx i))⁻¹) (2*c⁻¹):=by
    have hf(s): f s ≠0:= norm_pos_iff.mp (hc.trans_le (ht _)); let M(s:sun): ℂ≃ₗ[ℝ] ℂ := {
         toFun:=fun i=> f s*i
         invFun:=fun i=> (f s)⁻¹*i
         left_inv:=fun i=>inv_mul_cancel_left₀ (hf _) i
         right_inv:=fun i=>mul_inv_cancel_left₀ (hf _) i
         map_add':=fun x y=> mul_add ..
         map_smul':=fun x y=> mul_smul_comm .. }
    let F:=fun s:sun=> M (Muse.slash x hx s); let z:ℂ≃ₗ[ℝ] ℂ:=M Jams.tip
    have he i:‖z.symm i‖≤ c⁻¹*‖i‖:= (norm_mul ..).trans_le (by rw [norm_inv]; exact mul_le_mul_of_nonneg_right (inv_anti₀ hc (ht _)) (norm_nonneg _)) -- spelling
    have hy v: PaidBeam (fun i:sun=> F i v-z v) (|x| *a*‖v‖):=(bilimer (little hx h) (PaidBeam.static v)).stamp fun _=> (sub_mul ..).symm
    have hg:= PaidBeam.origin F z (mul_nonneg (abs_nonneg x) h.price) (inv_nonneg.mpr hc.le) he hp hy (PaidBeam.static (1:ℂ)); rw [norm_one,mul_one] at hg; exact hg.stamp fun i=> (show _= (f _ )⁻¹*1 from (mul_one _).symm)
end reciprocals
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.Feel.integrating
#print axioms YM.FullVolume.Nectar.little
