import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Representation of per-slot, per-test bounds

Formal estimates on functionals in kforms must give **derivative-address**
representations; bounding scalar evaluations alone does not pay the sum over
ordered field slots. Use Riesz extension per tape; no compatibility of the
witnesses across widths is needed.

Real signs via one extra Hahn extension on the double. Does not assert
mutual singularity of the resulting positive pair, not needed here.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Jetty
open scoped Topology ENNReal BigOperators Classical
open Function MeasureTheory Set CompactlySupported

section lift
variable {U : Type*} [AddCommGroup U][Module ℝ U]
variable {V : Type*} [NormedAddCommGroup V][NormedSpace ℝ V]

lemma lift (p : U→ₗ[ℝ] V)(hp : Injective p)(q : U→ₗ[ℝ] ℝ){K:ℝ}(hk:0≤K)
    (h : ∀ x:U, ‖q x‖ ≤ K*‖p x‖) : ∃ F : V →L[ℝ] ℝ, (∀ x, F (p x) = q x) ∧ ‖F‖≤K:=by
 let e:=LinearEquiv.ofInjective p hp
 let f:=q.comp e.symm.toLinearMap
 have he(x:U): (e x).1=p x:=rfl
 have hf(x:LinearMap.range p): ‖f x‖ ≤ K*‖x‖:=by
   change ‖q (e.symm x)‖ ≤ _
   apply (h _).trans_eq; rw [← he,e.apply_symm_apply];rfl
 obtain ⟨g,hg,hv⟩:= exists_extension_norm_eq (LinearMap.range p) (f.mkContinuous K hf)
 refine ⟨g,?_,hv.le.trans (LinearMap.mkContinuous_norm_le f hk hf)⟩
 intro x;rw [← he,hg];change q (e.symm (e x))=q x;rw [e.symm_apply_apply]
end lift

variable {X:Type*}[TopologicalSpace X][Nonempty X][CompactSpace X]
abbrev Air (X:Type*)[TopologicalSpace X]:= C(X,ℝ)
abbrev Signboard (X:Type*)[TopologicalSpace X]:=Air X×Air X
private def pin (a:ℝ):Air X:= ContinuousMap.const X a
private def mirror : ℝ × Air X →ₗ[ℝ] Signboard X where
 toFun p:= (pin p.1+p.2,pin p.1-p.2)
 map_add' p q:= by
   apply Prod.ext <;> apply ContinuousMap.ext <;> intro x
   · change (p.1+q.1)+(p.2 x+q.2 x)=p.1+p.2 x+(q.1+q.2 x);ring
   · change (p.1+q.1)-(p.2 x+q.2 x)=p.1-p.2 x+(q.1-q.2 x);ring
 map_smul' a p:=by
   apply Prod.ext <;> apply ContinuousMap.ext <;> intro x
   · change a*p.1+a*p.2 x=a*(p.1+p.2 x);ring
   · change a*p.1-a*p.2 x=a*(p.1-p.2 x);ring

private lemma shades (p:ℝ×Air X) : |p.1|+‖p.2‖ ≤ ‖mirror p‖:=by
 let b:=‖mirror p‖
 have hx(x:X): |p.1| + |p.2 x| ≤ b:=by
   have he:= (norm_prod_le_iff.mp (le_refl ‖mirror p‖))
   have h₁:= (ContinuousMap.norm_coe_le_norm (mirror p).1 x).trans he.1
   have h₂:= (ContinuousMap.norm_coe_le_norm (mirror p).2 x).trans he.2
   change ‖p.1+p.2 x‖ ≤ b at h₁; change ‖p.1-p.2 x‖ ≤ b at h₂
   rw [Real.norm_eq_abs,abs_le'] at h₁ h₂
   obtain h|h := le_total 0 p.1 <;> obtain h'|h' := le_total 0 (p.2 x) <;>
      simp [abs_of_nonneg, abs_of_nonpos, h, h'] <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2]
 have h':0≤b-|p.1|:=by
   let x:X:= Classical.ofNonempty
   linarith only [hx x,abs_nonneg (p.2 x)]
 have hs:= (ContinuousMap.norm_le p.2 h').mpr (fun x=> (Real.norm_eq_abs _).trans_le (by linarith only [hx x]))
 change _≤b;linarith only [hs]

private lemma flips : Injective (mirror (X:=X)):=by
 intro p p' he; have ht:= shades (p-p'); rw [map_sub,he,sub_self,norm_zero] at ht
 have hnn := abs_nonneg (p-p').1; have hnn' := norm_nonneg (p-p').2
 have hv: p-p'=0:= Prod.ext (abs_eq_zero.mp (by linarith)) (norm_eq_zero.mp (by linarith))
 exact sub_eq_zero.mp hv

private def nick (q : Air X→ₗ[ℝ] ℝ)(K:ℝ): ℝ×Air X →ₗ[ℝ] ℝ:= LinearMap.coprod (K • LinearMap.id) q

/-- Positive doubled extension. -/
theorem feather (q : Air X→ₗ[ℝ] ℝ){K:ℝ}(hk:0≤K)(h : ∀ x, |q x|≤K*‖x‖) :
    ∃ F: Signboard X→L[ℝ] ℝ, (∀ p:ℝ×Air X,F (pin p.1+p.2,pin p.1-p.2)=K*p.1+q p.2) ∧ ‖F‖≤K:=by
 have he(p:ℝ×Air X): ‖nick q K p‖≤K*‖mirror p‖:=by
   rw [Real.norm_eq_abs];change |K*p.1+q p.2| ≤_
   apply (abs_add_le ..).trans
   rw [abs_mul,abs_of_nonneg hk]
   exact (add_le_add_right (h _) _).trans ((mul_add K _ _).ge.trans (mul_le_mul_of_nonneg_left (shades p) hk))
 obtain ⟨F,hF,hv⟩:=lift mirror flips (nick q K) hk he
 exact ⟨F,hF,hv⟩

omit [Nonempty X] in
private lemma blessed (F: Signboard X→L[ℝ] ℝ){K:ℝ}
    (hF : F (pin 1,pin 1)=K)(hv: ‖F‖ ≤ K)(p: Signboard X)
    (hp: (∀ x, 0≤p.1 x) ∧ ∀ x, 0≤p.2 x): 0 ≤ F p:=by
 let x:Signboard X:= (pin 1,pin 1)
 have he{f:Air X}(h₁:∀ t,0≤f t)(h₂:‖f‖ ≤ ‖p‖): ‖‖p‖ • pin 1-f‖≤‖p‖:= (ContinuousMap.norm_le _ (norm_nonneg p)).mpr (fun t=>by
    rw [ContinuousMap.sub_apply,ContinuousMap.smul_apply,Real.norm_eq_abs,abs_le'];change ‖p‖ * 1-f t≤ _ ∧ -(‖p‖ * 1-f t)≤_
    have h:= (ContinuousMap.norm_coe_le_norm f t).trans h₂; rw [Real.norm_eq_abs,abs_le'] at h
    constructor <;> linarith [h₁ t,norm_nonneg p])
 have hs:= (norm_prod_le_iff.mp (le_refl ‖p‖))
 have h' : ‖‖p‖ • x-p‖≤‖p‖:= norm_prod_le_iff.mpr ⟨he hp.1 hs.1,he hp.2 hs.2⟩
 have hz: ‖F (‖p‖ • x -p)‖ ≤ K*‖p‖:= (F.le_opNorm _).trans (mul_le_mul hv h' (norm_nonneg _) ((norm_nonneg F).trans hv))
 rw [map_sub,map_smul,show F x=K from hF,Real.norm_eq_abs,abs_le'] at hz
 change ‖p‖*K-F p ≤ K*‖p‖ ∧ _ at hz; nlinarith only [hz.1]

variable [T2Space X][MeasurableSpace X][BorelSpace X]
omit [Nonempty X] in
theorem carrier (q:Air X→ₗ[ℝ] ℝ)(h: ∀ f:Air X,(∀ t,0≤f t)→0≤q f):
   ∃ μ:Measure X, IsFiniteMeasure μ ∧μ.real univ = q (pin 1) ∧ ∀ f:Air X,q f=∫ x,f x ∂μ:=by
 let Λ:C_c(X,ℝ) →ₚ[ℝ] ℝ:={
   toFun f:=q f.toContinuousMap
   map_add' f g:=map_add q ..
   map_smul' c f:=map_smul q ..
   monotone' f g hf:=by rw [←sub_nonneg,←map_sub]; exact h _ fun t=> sub_nonneg.mpr (hf t) }
 let μ:=RealRMK.rieszMeasure Λ
 have hm:IsFiniteMeasure μ:=by unfold μ; infer_instance
 have he (f:Air X):q f=∫ x,f x ∂μ:=by
   let g:C_c(X,ℝ):= {toContinuousMap:=f,hasCompactSupport':=HasCompactSupport.of_compactSpace _}
   exact (RealRMK.integral_rieszMeasure Λ g).symm
 refine ⟨μ,hm,?_,he⟩
 rw [he];simp [pin]

theorem render (q:Air X→ₗ[ℝ] ℝ){K:ℝ}(hk:0≤K)(h : ∀ x,|q x|≤K*‖x‖):
 ∃ μ ν:Measure X, IsFiniteMeasure μ ∧ IsFiniteMeasure ν ∧ μ.real univ+ν.real univ = K ∧
   ∀ f:Air X,q f = (∫ x,f x ∂μ)-(∫ x,f x ∂ν):=by
 obtain ⟨F,hF,hN⟩:=feather q hk h
 have he:F (pin 1,pin 1)=K:=by
   have ha:=hF (1,0); simpa using ha
 let A := F.toLinearMap.comp (LinearMap.inl ℝ (Air X) (Air X))
 let B := F.toLinearMap.comp (LinearMap.inr ℝ (Air X) (Air X))
 obtain ⟨μ,hμ,ha,hA⟩:= carrier A (fun f hf=>blessed F he hN (f,0) ⟨hf,fun _=>le_refl _⟩)
 obtain ⟨ν,hν,hb,hB⟩:= carrier B (fun f hf=>blessed F he hN (0,f) ⟨fun _=>le_refl _,hf⟩)
 have hp(f g:Air X):F (f,g)=A f+B g:=by change _=F (f,0)+F (0,g); rw [← map_add]; change _=F (f+0,0+g); simp
 refine ⟨μ,ν,hμ,hν,?_,fun f=>?_⟩
 · rw [ha,hb,← hp,he]
 · rw [←hA,←hB];have ht:=hF (0,f); dsimp only at ht
   rw [show pin (X:=X) 0=(0:Air X) from rfl,zero_add,zero_sub, mul_zero,zero_add,hp,map_neg] at ht
   simpa [sub_eq_add_neg] using ht.symm
end YM.RG08.Jetty
