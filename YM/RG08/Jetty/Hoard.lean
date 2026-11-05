import YM.RG08.Jetty.Cube

/-! # Offset presentation with literal derivative measures

No assumptions on compactness of kernel address support or uniqueness
of witnesses. Shrink width across *one* stage compression to
polynomial; repeated estimates use the exponential trial bound itself.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open Function MeasureTheory Filter Set
open scoped ContDiff NNReal Classical BigOperators
variable {d:ℕ}{σ τ K:ℝ}
def beam (d:ℕ)(h:0<σ)(f:Pearl):=‖gleam d h f‖
lemma beam_nn (d)(h:0<σ)(f):0≤beam d h f:=norm_nonneg _
lemma beam_le (d)(h:0<σ)(f:Pearl)(he:0≤K)(hv:∀ i:Jet d,∀ x:E4,|openJet i x f| ≤ K * Real.exp (σ*‖x‖)): beam d h f ≤ K:=by
 apply cloud_cap (gleam d h f) he _ (shine h f)
 intro i x; rw [gleam_at,abs_mul,abs_of_pos (warp_pos ..),warp,Real.exp_neg]
 exact (mul_inv_le_iff₀ (Real.exp_pos _)).mpr (hv _ _)
lemma beam_opens (d)(h:0<σ)(f:Pearl)(i:Jet d)(x:E4):|openJet i x f|≤beam d h f * Real.exp (σ*‖x‖):=by
 have he:= cloud_at (gleam d h f) i x
 rw [gleam_at,abs_mul,abs_of_pos (warp_pos ..),warp,Real.exp_neg] at he
 exact (mul_inv_le_iff₀ (Real.exp_pos _)).mp he
lemma beam_smaller {D:ℕ}(h:0<σ)(ht:0<τ)(hh:τ ≤ σ)(hb:d≤D)(f:Pearl):beam d h f≤ beam D ht f:=by
 apply beam_le _ h f (norm_nonneg _); intro i x
 let j:Jet D:=⟨⟨i.1,lt_of_lt_of_le i.1.isLt (by omega)⟩,i.2⟩
 exact (beam_opens _ ht _ j x).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hh (norm_nonneg _))) (beam_nn _ ht f))

def glory (σ:ℝ)(x:E4):ℝ≥0:= ⟨warp σ ‖x‖,(warp_pos ..).le⟩
@[fun_prop] lemma glory_meas : Measurable (glory σ):=by unfold glory warp; fun_prop
private lemma pay (x:E4)(r:ℝ):glory σ x • r=r*warp σ ‖x‖:=by rw [NNReal.smul_def]; exact mul_comm ..
def dark (σ:ℝ)(μ:Measure E4):Measure E4:= μ.withDensity (fun x=> ↑(glory σ x))
lemma night (μ:Measure E4)(σ:ℝ)(f:E4→ℝ):
   (Integrable f (dark σ μ) ↔ Integrable (fun x=> f x * warp σ ‖x‖) μ) ∧
   (∫ x,f x ∂dark σ μ)= ∫ x,f x * warp σ ‖x‖ ∂μ:=by
 rw [dark,integrable_withDensity_iff_integrable_smul glory_meas,integral_withDensity_eq_integral_smul glory_meas]; simp_rw [pay];simp

def Beacon (σ:ℝ)(x:E4):= Real.exp (σ*‖x‖)
@[fun_prop] lemma Beacon_cont : Continuous (Beacon σ):=by unfold Beacon;fun_prop
lemma Beacon_nn (σ x) : 0 ≤ Beacon σ x:= (Real.exp_pos _).le
lemma Beacon_one (h:0≤σ)(x) : 1 ≤ Beacon σ x:= Real.one_le_exp (mul_nonneg h (norm_nonneg _))
lemma budget (μ:Measure E4)[IsFiniteMeasure μ](σ:ℝ):
 Integrable (Beacon σ) (dark σ μ) ∧ (∫ x,Beacon σ x ∂dark σ μ)=μ.real univ:=by
 have he(x:E4): Beacon σ x * warp σ ‖x‖=1:=by unfold Beacon warp;rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
 have ht:=night μ σ (Beacon σ);simp_rw [he] at ht
 refine ⟨ht.1.mpr (integrable_const _),?_⟩
 rw [ht.2, integral_const]; simp
lemma Beacon.finite {μ:Measure E4}(h:0≤σ)(he:Integrable (Beacon σ) μ):IsFiniteMeasure μ:=by
 have ht: Integrable (fun (_:E4)=>(1:ℝ)) μ:= he.mono (by fun_prop) (by
   filter_upwards with x; simpa only [norm_one,Real.norm_eq_abs,abs_of_nonneg (Beacon_nn ..)] using Beacon_one h x)
 exact (integrable_const_iff.mp ht).resolve_left one_ne_zero

def Fest (d:ℕ)(σ C:ℝ)(q:Pearl→ℝ)(μ ν:Jet d→Measure E4):Prop:=(∀ s, IsFiniteMeasure (μ s)∧IsFiniteMeasure (ν s)∧Integrable (Beacon σ) (μ s)∧ Integrable (Beacon σ) (ν s)∧(∫ x,Beacon σ x ∂μ s)+(∫ x, Beacon σ x ∂ν s)≤ C) ∧
  ∀ f, (∀ s, Integrable (fun x=>openJet s x f) (μ s) ∧ Integrable (fun x=>openJet s x f) (ν s))∧
  q f=∑ s,((∫ x,openJet s x f ∂μ s)-(∫ x,openJet s x f ∂ν s))

lemma concert (d:ℕ)(h:0<σ)(q:Pearl→ₗ[ℝ] ℝ)(hK:0≤K)(hx:∀ f,|q f|≤K*beam d h f):∃ μ ν:Jet d→Measure E4,Fest d σ K q μ ν:=by
 obtain ⟨μ,ν,hμ,hf⟩:=presentation (gleam d h) q (gleaming h) (fun f i=>shine h f i) hK hx
 have he (f:Pearl)(s:Jet d):gleam d h f s ∘ push E4=(fun x=> openJet s x f * warp σ ‖x‖):=rfl
 refine ⟨fun s=>dark σ (μ s),fun s=>dark σ (ν s),fun s=>?_,fun f=> ?_⟩
 · obtain ⟨h₁,h₂,h₃⟩:=hμ s; have ha:=budget (μ s) σ; have hb:=budget (ν s) σ
   exact ⟨Beacon.finite h.le ha.1,Beacon.finite h.le hb.1, ha.1,hb.1,(congrArg₂ _ ha.2 hb.2 : _+_=(μ s).real univ+(ν s).real univ).trans_le h₃⟩
 obtain ⟨hI,hE⟩:=hf f;simp_rw [he] at hI
 refine ⟨fun s=>⟨(night _ _ _).1.mpr (hI s).1,(night _ _ _).1.mpr (hI s).2⟩,hE.trans ?_⟩
 exact Finset.sum_congr rfl fun s _=>congrArg₂ _ ((night (μ s) σ (fun x=>openJet s x f)).2.symm) ((night _ _ _).2.symm)
end YM.RG08.Jetty
