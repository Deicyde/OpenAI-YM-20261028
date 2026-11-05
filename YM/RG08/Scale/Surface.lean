import YM.RG08.Envoi.Sample
import Mathlib.RingTheory.PowerSeries.Expand
/-! # Formal squared coupling, orientation; tangent branch and compositional local price. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Conductor
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Push.AbsoluteSums UVExtension.Free PowerSeries
open scoped BigOperators Topology Real Classical
variable {I : Type} {y δ : I→ℝ} {r s : ℕ}
abbrev Cues := ℕ→ℝ

-- f(X_k)*W(X_k f(X_k)), X_k=g_k^2.
def glide (f W : Cues) : Cues := fun i=> coeff i (PowerSeries.mk f * PowerSeries.subst (Span f) (PowerSeries.mk W))
lemma glide_play (f W : Cues) : PowerSeries.mk (glide f W)= PowerSeries.mk f * PowerSeries.subst (Span f) (PowerSeries.mk W) := by ext n; rw [coeff_mk]; rfl
lemma glide_pose (f W : Cues) : Span (glide f W)=PowerSeries.subst (Span f) (Span W) := by
  have h: Span W=X* PowerSeries.mk W:=rfl
  rw [h,subst_mul spanning,subst_X spanning]; unfold Span; rw [glide_play,mul_assoc]

private lemma glide_sung (f W : Cues)(i:ℕ): glide f W i=∑ j∈range (i+1), W j * powT f (j+1) (i-j) := by
  have he V : coeff (i+1) (Span V)=V i:= by simp [Span]
  rw [← he (glide f W), glide_pose]; have hp:Span W=PowerSeries.mk (fun i=>coeff i (Span W)):= by ext; rw [coeff_mk]
  nth_rw 1 [hp]
  rw [merge_f,sum_range_succ']
  have hh j: coeff (j+1) (Span W)=W j:= by simp [Span]
  simp only [hh,coeff_zero_eq_constantCoeff_apply,Span,map_mul,constantCoeff_X,zero_mul,add_zero,Nat.add_sub_add_right]
lemma glide_tall {W f:Cues}(h : W 0=1)(hp:f 0=1): glide f W 0=1 := by simp [glide_sung,h,hp,powT]

def muse (W : Cues) : Cues := fun i=>coeff i (PowerSeries.mk W)⁻¹
lemma muse_stamp (W : Cues) : PowerSeries.mk (muse W)= (PowerSeries.mk W)⁻¹ := by ext; rw [coeff_mk]; rfl
lemma muse_unit {W : Cues}(h:W 0=1) : muse W 0=1 := by simp [muse,h]
private lemma portage (f : PowerSeries ℝ)(hf : HasSubst f) : PowerSeries.subst f (1:PowerSeries ℝ)=1:= by rw [← pow_zero (X:PowerSeries ℝ),PowerSeries.subst_pow hf,pow_zero,pow_zero]
theorem glide_toward (f W : Cues) : let a:= Span (glide f (reform W)); let b:= Span f; a=b* PowerSeries.subst a (PowerSeries.mk W) := by
   intro a b; have hh: a=b* PowerSeries.subst (Span f) (PowerSeries.mk (reform W)):= by unfold a Span; rw [glide_play,← mul_assoc]
   conv_lhs=> rw [hh]
   rw [reforms W,PowerSeries.subst_comp_subst_apply spanning spanning]; unfold a; rw [glide_pose] -- rewrites inside a too?
theorem glide_before (f W : Cues) (h : W 0=1): let a:=Span f; let b:= Span (glide f (muse W)); a=b* PowerSeries.subst a (PowerSeries.mk W) := by
   intro a b
   have hf : HasSubst a:=spanning
   have hh: b=a * PowerSeries.subst a (PowerSeries.mk W)⁻¹:= by unfold b Span; rw [glide_play,← mul_assoc, muse_stamp] -- ambiguous pow notation
   rw [hh,mul_assoc,← subst_mul hf,PowerSeries.inv_mul_cancel,portage a hf,mul_one]; rw [constantCoeff_mk,h]; simp

variable {W F H V : I→Cues} {e : ℕ}
lemma vanish_glide (f W : Cues) (h:W 0=1)(n) : glide f W (n+1)-f (n+1) = ∑ j∈range (n+1), W (j+1) * powT f (j+1+1) (n-j) := by
  rw [glide_sung,sum_range_succ',h,one_mul,powT,pow_one,coeff_mk,Nat.sub_zero]; simp
lemma grad_lease (h : ∀ i,W i 0=1)(hp:∀ i,V i 0=1)(he:Audience y)(hv:∀ j≤r, Lease y δ (fun i=> F i j) (fun i=> H i j)) (hc:∀ j≤r+1, Lease y δ (fun i=> W i j) (fun i=> V i j)) : Lease y δ (fun i=> glide (F i) (W i) (r+1)- F i (r+1)) (fun i=>glide (H i) (V i) (r+1)-H i (r+1)) := by
  simp_rw [vanish_glide _ (W _) (h _),vanish_glide _ (V _) (hp _)]
  apply Lease.lists; exact he
  intro i hi; have hz:=mem_range.mp hi; exact (hc (i+1) (by omega)).times (Lease.powerT he hv _ _ (by omega)) he
end YM.RG08.Conductor
