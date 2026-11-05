import YM.WilsonBulk.Recast.Fix

/-! # Recover positive ratio contacts; two-sided formal substitution. -/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Recall
open Function Filter PowerSeries Finset Equiv Sheet
open scoped Topology Classical BigOperators
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℝ A] [Algebra ℝ B] {p g r q : PowerSeries A} {n : ℕ}
omit [Algebra ℝ A] in
lemma rec_one (he : constantCoeff p=1) : recover p*p=1 := recover_mul (unit_const_one he)
omit [Algebra ℝ A] in
lemma crown (hp : constantCoeff p=1) : constantCoeff (recover p)=1 := by simpa only [map_mul, hp,mul_one,map_one] using congr_arg constantCoeff (rec_one hp)
omit [Algebra ℝ A] in
lemma reclaim (h : constantCoeff p=1) (he : q*p=1) : q=recover p := by
  calc q = q* (p*recover p) := by rw [mul_comm p,rec_one h,mul_one]
       _ = recover p := by rw [← mul_assoc,he,one_mul]
omit [Algebra ℝ A] in
lemma reship (h : constantCoeff p=1) : recover (recover p)=p := by symm; apply reclaim (crown h); rw [mul_comm,rec_one h]
-- direct expression ρ^2 ω=1 and its near equivalence.

def yesterday (Ω : PowerSeries A) := recover (arises Ω)
lemma counterpart (h : constantCoeff p=1) :
    let g:= yesterday p; constantCoeff g=1 ∧ g^2*p=1 := by
  intro g; obtain ⟨hp,hh⟩:= arises_rule h; refine ⟨crown hp,?_⟩; nth_rw 1 [← hh]; rw [← mul_pow]; rw [show g*(arises p)=1 from rec_one hp,one_pow]
lemma yesterday_only (h : constantCoeff p=1) (hq : constantCoeff g=1) (he : g^2*p=1) : g=yesterday p := by
  have hp : p=(recover g)^2:= reclaim (p:=g^2) (by rw [map_pow,hq, one_pow]) (by rw [mul_comm]; exact he) |>.trans (Eq.symm (reclaim (p:=g^2) (by rw [map_pow,hq,one_pow]) (by rw [← mul_pow,rec_one hq,one_pow])))
  rw [yesterday,← arises_only h (crown hq) hp.symm, reship hq]
lemma reverse_ratios (h : constantCoeff p=1) : bar (polling p) (yesterday p)= recover (polling p) := by
  obtain ⟨hx,hq⟩:= poll_rule h
  have hp : constantCoeff (bar (polling p) p)=1:= by rw [bar_const, h]
  refine Eq.trans (yesterday_only (p:=bar (polling p) p) hp (by rw [bar_const,(counterpart h).1]) ?_) ?_
  · rw [← map_pow,← map_mul,(counterpart h).2,map_one]
  exact (yesterday_only hp (crown hx) (by rw [← hq,← mul_pow,rec_one hx,one_pow])).symm
-- consume trigonometry as authority on both coupling directions
lemma bar_ext_aux (u v : PowerSeries A→ₐ[ℝ]PowerSeries B) (he : constantCoeff (u X)=0) (hh : u X=v X) (hp : ∀ a, u (C a)=v (C a)) : u=v := by
  let F:A→ₐ[ℝ] PowerSeries B := v.comp (post _)
  rw [tuning F u he hp, tuning F v (by rw [← hh]; exact he) (fun _=>rfl)]; congr 1
lemma noiseless (q p : PowerSeries A) (h : bar q (tempo p)=X) (v : PowerSeries A) : bar q (bar p v)=v := DFunLike.congr_fun (f:=(bar q).comp (bar p)) (g:=AlgHom.id ..) (bar_ext_aux _ _ (by rw [AlgHom.comp_apply,bar_X,bar_const]; simp) (by rw [AlgHom.comp_apply, bar_X]; exact h) (fun i=> by rw [AlgHom.comp_apply,bar_C,bar_C]; rfl)) _
-- injective even with Nilpotent coefficients. triangular on n≥1. Needed for other direction. Implementation no Mathlib_subst details required
lemma bar_injective (p : PowerSeries A) (hp : constantCoeff p=1) : Injective (bar p) := by
  intro u v h; ext1 i; induction i using Nat.strong_induction_on with
  | h i ih=>
     have hx : coeff i (1*bar p u)=coeff i (1*bar p v):= by rw [h]
     have hd : coeff (i-i) (p^i*(1:PowerSeries A))=1:= by rw [tsub_self,coeff_zero_eq_constantCoeff, mul_one,map_pow,hp,one_pow]
     rw [bar_terms,bar_terms,sum_range_succ,sum_range_succ,hd,one_mul,one_mul] at hx
     exact add_left_cancel (by rwa [sum_congr rfl (fun k (hk:k∈range i)=> congr_arg (fun x:A=> coeff (R:=A) _ _ * x) (ih k (mem_range.mp hk)))] at hx)
lemma castoff (h : constantCoeff p=1) : bar (polling p) (tempo (yesterday p))=X := by rw [tempo,map_mul,bar_X,reverse_ratios h,mul_assoc,mul_comm (polling _), rec_one (poll_rule h).1,mul_one]
lemma coastal (h : constantCoeff p=1) : bar (yesterday p) (tempo (polling p))=X := by apply bar_injective _ (poll_rule h).1; rw [noiseless _ _ (castoff h),bar_X]; rfl
end YM.WilsonBulk.Recall
