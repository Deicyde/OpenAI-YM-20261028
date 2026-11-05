import YM.WilsonBulk.Series.Possess
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Submit arbitrary palette in analytic transformations

Encode rescaled log-link coordinates `log U(g)/g`, ALWAYS analytic at flat
in the called chart. Rules through scaling clocks built elsewhere. Handle
exp series exactly for log-Haar ratio identities.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
open scoped Classical BigOperators Topology ContDiff
open Finset Function PowerSeries Filter
variable {A E : Type} {α β : Type} [CommRing A] [NormedAddCommGroup E] [NormedSpace ℝ E]
-- downclock

def zoom (p : PowerSeries A) : PowerSeries A := mk (fun i=>coeff (i+1) p)
lemma zoom_power (p : PowerSeries A) (n : ℕ) : coeff n (zoom p) = coeff (n+1) p := coeff_mk ..
lemma zoom_const (p : PowerSeries A) : constantCoeff (zoom p)=coeff 1 p := by rw [← coeff_zero_eq_constantCoeff,zoom_power]
lemma zoom_key {p : PowerSeries A} (hp : constantCoeff p=0) : X*zoom p = p := by ext1 i; cases i with
  | zero=> rw [coeff_zero_X_mul,coeff_zero_eq_constantCoeff,hp]
  | succ i=> rw [coeff_succ_X_mul,zoom_power]
lemma zoom_X (p : PowerSeries A) : zoom (X*p)=p := by ext1 n; rw [zoom_power,coeff_succ_X_mul]
lemma zoom_agrees {n} {p q : PowerSeries A} (hp : Steps (n+1) p q) : Steps n (zoom p) (zoom q) := fun i hi=> by rw [zoom_power,zoom_power,hp (i+1) (by omega)]
namespace Sheet
variable [Fintype α] {f g : Tabletop α→ℝ}
-- write RT z/g

def flash (f : Tabletop α→ℝ) := zoom (ink f)
lemma flash_const (hf : ContDiffAt ℝ ω f 0) : constantCoeff (flash f)=∑ i,MvPolynomial.C (leafD i f 0)*MvPolynomial.X i := by rw [flash,zoom_const,ink_grade1 hf]
lemma ink_root (hp : f 0=0) : constantCoeff (ink f)=0 := by rw [ink_norm,hp,map_zero]
lemma flash_origin (hp : f 0=0) : X*flash f= ink f := zoom_key (ink_root hp)
lemma flash_time (hp : f 0=0) : X* clockD _ (flash f) + flash f= clockD _ (ink f) := by rw [← flash_origin hp,D_leib,clock_X,one_mul,add_comm]
lemma flash_player (hf : ContDiffAt ℝ ω f 0) (hp : f 0=0) (i : α) : player i (flash f)=ink (leafD i f) := by apply X_mul_cancel; rw [← ink_player hf]; rw [← flash_origin hp,D_leib,show player i X=0 from parallelD_X _,zero_mul,zero_add]
lemma flash_expands (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) (hp : f 0=0) (hq : g 0=0) : flash (f+g)= flash f+flash g := by apply X_mul_cancel; rw [flash_origin (f:=f+g) (by simp [hp,hq]),mul_add,ink_add hf hg,flash_origin hp,flash_origin hq]
lemma ink_scale (hf : ContDiffAt ℝ ω f 0) (r : ℝ) : ink (r • f)=r • ink f := by
  let p : Tabletop α→ℝ:=fun _=>r
  rw [show r • f=p*f from rfl,ink_mul (f:=p) contDiffAt_const hf, show ink p=C (MvPolynomial.C r) from ink_const r,MvPolynomial.C_eq_algebraMap,← PowerSeries.algebraMap_apply, Algebra.smul_def]
lemma ink_real_exp (hf : ContDiffAt ℝ ω f 0) (hp : f 0=0) : ink (Real.exp ∘ f) = tide (ink f) := by
  let g:= Real.exp ∘ f
  have hg : ContDiffAt ℝ ω g 0:= Real.contDiff_exp.contDiffAt.comp (x:=0) hf
  refine column_ode_id (clockD _ (ink f)) ?_ ?_ ?_
  · rw [ink_norm,comp_apply,hp,Real.exp_zero,map_one,tide_const]
  · have he (i) : leafD i g=ᶠ[𝓝 0] leafD i f*g := by
      filter_upwards [hf.eventually (by simp)] with x hx; unfold g Function.comp; simp only [leafD,Pi.mul_apply,Analysis.D,fderiv_exp (hx.differentiableAt (by simp)),_root_.smul_apply,smul_eq_mul]; rw [mul_comm]
    change clockD _ (ink g)=_*ink g; rw [ink_time hf,ink_time hg,sum_mul]; refine sum_congr rfl fun i _=> ?_
    rw [ink_of (he i),ink_mul (leaf_at i hf) hg]; ring
  rw [differentiate_time (ink_root hp)]; ring
variable [Fintype β]
variable {F : Tabletop β→ Tabletop α}
def exposure (F : Tabletop β→Tabletop α) : α → Tape β := fun i=> flash (fun v=>F v i)
lemma leaf_α (j : β) (hf : ContDiffAt ℝ ω f 0) (hF : ContDiffAt ℝ ω F 0) (hz : F 0=0) :
    leafD j (f ∘ F)=ᶠ[𝓝 0] ∑ i:α,(leafD i f ∘ F)*leafD j (fun z=>F z i) := by
  filter_upwards [hF.eventually (by simp),hF.continuousAt.tendsto.eventually ((show ContDiffAt ℝ ω f (F 0) by rwa [hz]).eventually (by simp))] with x hu hv
  have h₁ := hu.differentiableAt (by simp)
  let L (i:α) := ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:α=>ℝ) i
  have ht i : leafD j (fun z=> F z i) x = leafD j F x i := by
    change Analysis.D (spike j) (L i∘ F) x = _; unfold Analysis.D; rw [fderiv_comp x (L i).differentiableAt h₁,(L i).fderiv]; rfl
  rw [leafD,Analysis.D,fderiv_comp x (hv.differentiableAt (by simp)) h₁]
  change fderiv ℝ f (F x) (leafD j F x)= _
  rw [spike_all (leafD j F x), map_sum, Finset.sum_apply]; apply sum_congr rfl fun i _=>?_; rw [Pi.mul_apply, ht, map_smul, smul_eq_mul,mul_comm]; rfl

lemma ink_comp_time (hf : ContDiffAt ℝ ω f 0) (hz : F 0=0) :
    clockD _ (submit (exposure F) (ink f)) = ∑ i:α,submit (exposure F) (ink (leafD i f))*clockD _ (ink (fun v=>F v i)) := by
  rw [clock_chain,ink_time hf,map_sum]; simp_rw [map_mul, submit_named, ink_player hf, map_mul,submit_X]; rw [← sum_add_distrib]; refine sum_congr rfl fun i _=>?_; rw [← flash_time (f:=fun v=>F v i) (by simp [hz])]; unfold exposure; ring
lemma ink_comp (hf : ContDiffAt ℝ ω f 0) (hF : ContDiffAt ℝ ω F 0) (hz : F 0=0) : ink (f ∘ F)=submit (exposure F) (ink f) := by
  ext1 n; induction n using Nat.strong_induction_on generalizing f with
  | h n ih=>
    cases n with
    | zero=>
      simp only [coeff_zero_eq_constantCoeff, submit,code,tuner_const,ink_norm,comp_apply, hz]
      rw [MvPolynomial.aeval_C, PowerSeries.algebraMap_apply, constantCoeff_C]; rfl
    | succ n=>
      have he (i) : ContDiffAt ℝ ω (fun z=> F z i) 0 := contDiffAt_pi.mp hF i
      have hh : ContDiffAt ℝ ω f (F 0) := by rwa [hz]
      refine smul_right_injective _ (show ((n+1:ℕ):ℝ)≠0 by positivity) ?_
      dsimp only
      rw [← clock_coeff,← clock_coeff,ink_time (hh.comp 0 hF), ink_comp_time hf hz]
      simp_rw [ink_of (leaf_α _ hf hF hz),ink_sum _ _ (fun i _=> show ContDiffAt ℝ ω ((leafD i f ∘ F)* _) _ from (((show ContDiffAt ℝ ω (leafD i f) (F 0) by rw [hz]; exact leaf_at i hf).comp 0 hF).mul (leaf_at _ (he i)))), sum_mul,ink_mul ((show ∀ i,ContDiffAt ℝ ω (leafD i f ∘ F) 0 from fun i=> (show ContDiffAt ℝ ω (leafD i f) (F 0) by rw [hz]; exact leaf_at i hf).comp 0 hF) _) (leaf_at _ (he _)),ink_time (he _), mul_sum]
      rw [sum_comm]; simp only [map_sum,mul_assoc]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_; exact (Steps.mul (n:=n+1) (fun i hi=>ih i hi (leaf_at _ hf)) Steps.self) n (by omega)

lemma flash_comp (hf : ContDiffAt ℝ ω f 0) (hp : f 0=0) (hF : ContDiffAt ℝ ω F 0) (hz : F 0=0) : flash (f ∘ F)=submit (exposure F) (flash f) := by apply X_mul_cancel; rw [flash_origin (f:=f ∘ F) (by rw [comp_apply,hz,hp]),ink_comp hf hF hz,← flash_origin hp,map_mul,submit_X]
omit [Fintype β] in
lemma flash_of (he : f=ᶠ[𝓝 0] g) : flash f=flash g := congr_arg zoom (ink_of he)
omit [Fintype β] in
lemma flash_named (i : α) : flash (fun z : Tabletop α=>z i)=named i := by unfold flash; rw [ink_named,zoom_X]
omit [Fintype β] in
lemma exposure_id : exposure (id : Tabletop α→Tabletop α)=named := funext flash_named
end Sheet
end YM.WilsonBulk
