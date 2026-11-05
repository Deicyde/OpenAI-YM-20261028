import YM.UVExtension.Beach.Eye
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Beach
open Function Filter Set Metric Lattice RG Wilson
open Extraction Fallow Poppy Tide Swell Lamppost Spire Pier Rafter BoundedContinuousFunction MeasureTheory
open scoped Topology BigOperators Classical ContDiff Interval
variable {a:ℝ} (ha:0<a)
local notation "V"=> Row a
local notation "Z"=> ball (0:ℂ) a
section
variable {A: Type}[TopologicalSpace A] (f:ℝ→A)
-- clamp outside
private lemma tunnel (hf: Continuous f)(x:ℝ): ∃ L:(A→ᵇℂ)→L[ℂ]ℂ,∀ v,L v=∫ i in 0..x,v (f i):= by
   have hp (v:A→ᵇℂ) : IntervalIntegrable (fun i=> v (f i)) volume 0 x:= (v.continuous.comp hf).intervalIntegrable ..
   let P:(A→ᵇℂ)→ₗ[ℂ]ℂ:=
     { toFun := fun v=> ∫ i in 0..x,v (f i)
       map_add' := fun v w=> intervalIntegral.integral_add (hp v) (hp w)
       map_smul' := fun k v=> by change _ = k * _; simp only [BoundedContinuousFunction.smul_apply,smul_eq_mul, intervalIntegral.integral_const_mul] }
   refine ⟨P.mkContinuous (|x-0|) (fun v=>?_ ),fun v=>rfl⟩; exact (intervalIntegral.norm_integral_le_of_norm_le_const (f:=fun i:ℝ=> v (f i)) (fun i _=> v.norm_coe_le_norm _)).trans_eq (mul_comm ..)
end
section
variable {I:Type}[NormedAddCommGroup I][NormedSpace ℝ I] [LocallyCompactSpace I]{S:Set I}(ho:IsOpen S)
variable {F G:ℂ→I→ℂ}{Y Z':ℕ→ℂ→I→ℂ}(h:Stamp a S F Y)(hp: Stamp a S G Z') (i:I) (x:I)(hx:x∈S)
local notation "y"=> fun (t:ℝ)=> x+t • i
variable (he:∀ d:Row a,∀ x∈ S,HasDerivAt (fun t:ℝ=>F d.val (x+t • i)) (G d.val x) 0)
include hx i ho h hp he ha
-- derivative identified also away from diameter by short-line FTC
lemma moved (z:ℂ)(hz:z∈ Z): HasDerivAt (fun t:ℝ=> F z (x+t • i)) (G z x) 0:=by
    let f:= fun t:ℝ=>x+t • i; have hf: Continuous f:=by unfold f; fun_prop
    obtain ⟨r,hr,hR⟩:= nhds_basis_ball.mem_iff.mp (show f ⁻¹' S∈ 𝓝 (0:ℝ) from hf.continuousAt.preimage_mem_nhds (ho.mem_nhds (by simpa [f])))
    let t:=r/2; have ht:0<t:=half_pos hr; let A:=f '' (ball (0:ℝ) r); let b:=Icc (-t) t; let c:=Ioo (-t) t; let X:= f '' b; have hX:X⊆ S:=by
       rintro _ ⟨i,hi,rfl⟩; exact hR (mem_ball_zero_iff.mpr ((abs_le.mpr hi).trans_lt (half_lt_self hr))) -- supply hr
    have hK : IsCompact X:= (isCompact_Icc.image hf); obtain ⟨P,hP,-,hY⟩:= hp.debt X hX hK
    let V'(v:ℝ):X:= ⟨f (min t (max (-t) v)), mem_image_of_mem _ (show _∈ b from ⟨le_min (by linarith) (le_max_left ..), min_le_left ..⟩)⟩; have hV : Continuous V':= by apply Continuous.subtype_mk; exact hf.comp (continuous_const.min (continuous_const.max continuous_id)) -- constant order
    have hB (v)(hv:v∈ b): (V' v).val=f v:=by dsimp only [V']; rw [max_eq_right hv.1,min_eq_right hv.2]
    have h₀(d:ℂ)(hd:d∈Z)(v)(hv:v∈b): P d (V' v)= G d (f v):=by exact (hY _ hd|>.symm).trans (congr_arg (G d) (hB v hv)) -- elaboration
    have hC : 0∈c:=⟨neg_lt_zero.mpr ht,ht⟩
    let q(d:ℂ) v:= P d (V' v); have hq(d:ℂ): Continuous (q d):=(P d).continuous.comp hV
    have hG(v)(hv:v∈ c): F z (f v)=F z (f 0)+∫ k in (0:ℝ)..v,q z k:=by
       obtain ⟨L,hL⟩:= tunnel V' hV v; have hm(i:ℝ)(hi:i∈c): f i∈ S:= hX (mem_image_of_mem _ (Ioo_subset_Icc_self hi))
       let T:= desk a ha; have he': Bumps Z (fun z=> F z (f 0)+ L (P z)):= bends_add (bumps _ _ ((h.analytic _ (hm _ hC)).differentiableOn)) (bumps _ _ (L.differentiable.comp_differentiableOn hP.differentiableOn))
       rw [← show L (P z)=_ from (show L (P z)=(∫ k in (0:ℝ)..v,q z k) from hL _)]
       refine T.agrees (fun z=>F z (f v)) _ (bumps _ _ ((h.analytic _ (hm v hv)).differentiableOn)) he' (fun d:Row a=>?_) hz
       let x:ℂ:= d.val; have he : (∫ k in (0:ℝ)..v,q x k)= F x (f v)- F x (f 0):=by
           refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=fun k=>F x (f k)) (fun k hk=> ?_) ((hq x).intervalIntegrable ..); have hh: k∈ c:= ordConnected_Ioo.uIcc_subset hC hv hk -- lemma name
           have ht : (fun w:ℝ=>F x (f k+w • i)) ∘ (fun r:ℝ=>r-k)=fun r:ℝ=> F x (f r):=by funext; simp [f,add_assoc, sub_smul]
           have h1 := he d (f k) (hm k hh); have h₂ : HasDerivAt (fun r:ℝ=>r-k) 1 k:= by simpa using (hasDerivAt_id' k).sub_const k
           have h₃:HasDerivAt (fun w:ℝ=> F x (f k+w • i)) (G x (f k)) ( (fun r:ℝ=>r-k) k):=by simpa using h1
           rw [show q x k= _ from (show q x k= G x (f k) from h₀ x (T.within d) k (Ioo_subset_Icc_self hh)),← ht]; exact (HasDerivAt.scomp k (h:=fun r:ℝ=> r-k) h₃ h₂).congr_deriv (one_smul _ _)
       change F x (f v)=F x (f 0)+ L (P x); rw [show L (P x)= (∫ k in (0:ℝ)..v,q x k) from hL _, he]; abel
    have hp:= intervalIntegral.integral_hasDerivAt_right ((hq z).intervalIntegrable 0 0) ((hq z).stronglyMeasurable.stronglyMeasurableAtFilter) (hq z).continuousAt
    have he:q z 0= G z x:= (h₀ z hz 0 (Ioo_subset_Icc_self hC)).trans (congr_arg (G z) (show f 0=x by simp [f]))
    refine he ▸ ((hp.const_add (F z (f 0))).congr_of_eventuallyEq (Eventually.mono (p:=fun x=>x∈c) (isOpen_Ioo.mem_nhds hC) (fun i hi=>hG i hi)))
end
end YM.UVExtension.Beach
