import YM.UVExtension.Lamppost.Capsule
import YM.UVExtension.Eyelet.Boot
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
/-! # Closed-span version, lifting complex tests with weak identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice RG Topology Set Push.AbsoluteSums Metric BoundedContinuousFunction
open Lamppost Eyelet
open scoped BigOperators Classical
variable {A B D Z E U : Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    [NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E]
    [NormedAddCommGroup U][NormedSpace ℂ U]
    (T:Opening D Z)
lemma tests (x:U)(hp:∀ L:U→L[ℂ] ℂ,L x=0): x=0:=by
    obtain ⟨g,h,he⟩:= exists_dual_vector'' ℂ x; refine norm_eq_zero.mp (Complex.ofReal_injective ?_); change Complex.ofReal ‖x‖= Complex.ofReal 0; rw [Complex.ofReal_zero]; exact he.symm.trans (hp g) -- RCLike cast
section lift
variable (r:D→E)(f: Z→U)(he:Bumps T.span f)(x:ℝ)(hx:0≤ x)(hp:∀ (S:Finset D)(p:D→ℂ), ‖∑ i∈S,p i • r i‖ ≤ x*‖∑ i∈S,p i • f (T.call i)‖)
variable [CompleteSpace U]
include he hx hp
lemma reflectV : ∃ g:Z→E,Bumps T.span g∧ (∀ d,g (T.call d)=r d)∧∀ z∈T.span,‖g z‖≤x*‖f z‖:=by
    let F:= Finsupp.linearCombination ℂ (f ∘ T.call); let L:= Finsupp.linearCombination ℂ r; let K:= Eyelet.boxes F; let P:= Eyelet.twig F
    let Q:= L.extendOfNorm P; have hv:= Eyelet.steams F; have hp' (v): ‖L v‖≤ x*‖P v‖:=hp _ v
    have hQ (v): Q (P v)=L v:= LinearMap.extendOfNorm_eq hv ⟨_,hp'⟩ _
    have hm (v): ‖Q v‖≤ x*‖v‖:= hv.induction_on v (isClosed_le Q.continuous.norm (continuous_const.mul continuous_norm)) (fun i=> by rw [hQ]; exact hp' i)
    have hk [IsClosed (K:Set U)] (z:Z)(hz:z∈T.span):f z∈ K:=by
       suffices hg: K.mkQL (f z)=0 from Submodule.Quotient.mk_eq_zero _|>.1 hg
       apply tests
       intro L
       exact T.agrees (fun z=> L (K.mkQL (f z))) (fun _=>0) (fun s p hs hh ht=> (L.comp K.mkQL).differentiable.comp_differentiableOn (he s p hs hh ht)) (bumps _ _ (differentiableOn_const _)) (fun d=> by change L (K.mkQL (f (T.call d)))=0; rw [show K.mkQL (f (T.call d))=0 from ?_,map_zero]; apply Submodule.Quotient.mk_eq_zero _|>.2; exact (LinearMap.range F).le_topologicalClosure ⟨Finsupp.single d 1,by simp [F]⟩) hz
    letI : IsClosed (K:Set U):= isClosed_closure
    let G(z): Quoit F:= if h:z∈T.span then ⟨f z,hk z h⟩ else 0; have hF z(h:z∈T.span): (G z).val=f z:= by unfold G; rw [dif_pos h]
    have hG:Bumps T.span G:=by
       intro s g hs hh ht; refine (YM.Analysis.lift_weak (range (fun L:U→L[ℂ] ℂ=> L.comp K.subtypeL)) ?_ hs ?_ ?_).differentiableOn
       · intro i j hi; refine Subtype.ext (sub_eq_zero.mp (tests _ (fun v=>?_))); rw [map_sub]; exact sub_eq_zero.mpr (hi (v.comp K.subtypeL) (mem_range_self _))
       · refine IsEmbedding.subtypeVal.isInducing.continuousOn_iff.mpr ((he s g hs hh ht).continuousOn.congr (fun i hi=> hF _ (hh hi)))
       rintro _ ⟨L,rfl⟩; exact (L.differentiable.comp_differentiableOn (he s g hs hh ht)).congr (fun i hi=> congr_arg L (hF _ (hh hi)))
    refine ⟨Q ∘ G,fun s g hs hh ht=> Q.differentiable.comp_differentiableOn (hG s g hs hh ht),fun d=>?_,fun z hz=>?_⟩
    · change Q (G _)= _; let v:= Finsupp.single d (1:ℂ); have hv: L v =r d:=by simp [L,v]
      change Q (G _)= _; rw [show G (T.call d)=P v from Subtype.ext ?_,hQ,hv]; rw [hF _ (T.within _)]; change _=F v; simp [F,v]
    exact (hm _).trans_eq (congr_arg (x * ·) (show ‖G z‖= ‖f z‖ from congr_arg norm (hF z hz)))
end lift
variable (M : Meter.{0,0,0} A B)
-- constant charge. extend on span
structure Stalk (M : Meter.{0,0,0} A B)(T:Opening D Z)(r:D→ M.CSlot)(a:ℝ):Prop where
    rises : ∃ f: Z→ M.CSlot,(∀ i k,Bumps T.span (fun z=> f z i k)) ∧ (∀ d,f (T.call d) = r d)∧∀ z∈T.span,M.MeasureP (f z) a
variable {M T}
open Meter
lemma combines {K:Type*} {c:K→M.CSlot} {b:K→ℂ} (s:Finset K) (q:M.Finger): Finger.issue M q (fun i j=>∑ k∈s,b k*c k i j)=∑ k∈s,b k*Finger.issue M q (c k):= by
  unfold Finger.issue
  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro i _
  unfold padding; cases q.engage i; simp only [Option.elim']; simp; dsimp only [Option.elim']; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _=> (by ring)
lemma sprigs {r:D→M.CSlot}{a x:ℝ} (h: Stalk M T r a)(ha:0≤a) (hx:0≤x)(v:D→E)(hp:∀ (S:Finset D)(p:D→ℂ) (c:ℝ), 0≤ c→ M.MeasureP (fun i k=>∑ j∈S,p j*r j i k) c → ‖∑ i∈S,p i • v i‖≤x*c):∃ g:Z→E,Bumps T.span g∧ (∀ d,g (T.call d)=v d)∧∀ z∈T.span, ‖g z‖≤2*x*a:=by
   obtain ⟨q,hq,ht,hh⟩:=h.rises
   letI : TopologicalSpace (M.Finger):=⊥; letI : DiscreteTopology M.Finger:= discreteTopology_bot _
   have hF z (hz:z∈T.span) t:‖Finger.issue M t (q z)‖ ≤ a:= M.spare (hh z hz) t
   let f(z): M.Finger →ᵇ ℂ:= if hz:z∈T.span then ofNormedAddCommGroupDiscrete (fun t=> Finger.issue M t (q z)) a (hF z hz) else 0
   have hf t z (hz:z∈T.span): f z t=Finger.issue M t (q z):=by unfold f; rw [dif_pos hz]; rfl
   have hg:Bumps T.span f:= by
       apply canal _ _ ha
       · intro i U g h he hv; exact (M.pollen hq i _ _ h he hv).congr (fun v hv=> hf i _ (he hv))
       intro z hz i; rw [hf _ _ hz]; exact hF z hz i
   have he(S:Finset D)(p:D→ℂ): let R:= (∑ i∈S,p i • f (T.call i)); ‖∑ i∈S,p i • v i‖≤2*x*‖R‖:=by
       intro R
       rw [show 2*x*‖R‖=x*(‖R‖+‖R‖) by ring]; refine hp S p _ (by positivity) (M.c_clips _ _ ?_); intro q'
       rw [combines, show ∑ _i∈S,p _i*Finger.issue M q' (r _i) = R q' from ?_]; exact R.norm_coe_le_norm _
       let L:(M.Finger →ᵇ ℂ)→L[ℂ]ℂ:= evalCLM ℂ q'; change _=L R; unfold R; rw [map_sum]; refine Finset.sum_congr rfl (fun i _=>?_); rw [map_smul]; change _=p i*f (T.call i) q'; rw [hf _ _ (T.within _),ht]
   obtain ⟨g,hg,hr,h'⟩:= reflectV T v f hg _ (mul_nonneg zero_le_two hx) he; exact ⟨g,hg,hr,fun z hz=> (h' z hz).trans (mul_le_mul_of_nonneg_left ((BoundedContinuousFunction.norm_le ha).2 (fun i=>by rw [hf _ _ hz]; exact hF _ hz _)) (by positivity))⟩
end YM.UVExtension.Rafter
