import YM.MergeProof.North.GraceN
import YM.MergeProof.West.Geo
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Acme
open Filter Set Function MeasureTheory Analysis Extraction Table Ward Climb Cells Next.UVStress Wilson Lattice Around Accent
open scoped Topology ContDiff BigOperators Classical
open Ribbons
lemma mars (D:ℕ) :∃ P:ℝ,0<P ∧∀ (r a ε:ℝ), 0<a → 0<ε→ arm D*a≤r/128→ ∀ (f:E4→ℂ),
 (∀ x∈ arena r, taper a x=Set.univ → ‖f x‖ ≤ ε) →
 (∀ j:Axis,∀ x:E4,(∀ t∈Icc (-arm D) (arm D), chord j x a t∈ arena r)→
    ∃ z: ℕ→ℝ→ℂ, z 0=f ∘ chord j x a ∧ (∀ i<D,∀ t∈Icc (-arm D) (arm D),HasDerivAt (z i) (z (i+1) t) t) ∧ ∀ t∈Icc (-arm D) (arm D), ‖z D t‖ ≤ ε)→
 ∀ y∈annulus r, ‖f y‖ ≤ ε*P:=by
   obtain ⟨A,hA,h⟩:= angel D _ (arm_pos D); refine ⟨(1+A)^4,pow_pos (by linarith) _,fun r a ε ha he hp f hv hf y hy=>?_⟩
   have hr:0<r:=by linarith only [hp,mul_pos (arm_pos D) ha]
   have ht (K:Finset Axis)(x:E4)(hh: ∀ i∉K,i∈taper a x) (hz: ‖x-y‖+ (K.card:ℝ)*(r/128) ≤ r/16): ‖f x‖ ≤ ε*(1+A)^K.card:=by
      induction K using Finset.induction_on generalizing x with
      | empty =>
         simp only [Finset.card_empty,pow_zero,mul_one]; apply hv x;swap
         · exact Set.eq_univ_of_forall fun j=> hh j (by simp)
         have he' : chord 0 x a 0∈arena r:= mitten a r 0 (arm D) hr (arm_pos _|>.le) ha hp x y 0 ⟨by linarith [arm_pos D],(arm_pos D).le⟩ (by simpa using hz) hy
         simpa [chord,Ward.inc] using he'
      | @insert i K hi ih=>
         simp only [Finset.card_insert_of_notMem hi,Nat.cast_add,Nat.cast_one] at hz ⊢
         have hk:= (mul_nonneg (show 0 ≤ (K.card+1:ℝ) by positivity) (show 0 ≤ r/128 by positivity)); obtain ⟨z,H0,H,hz'⟩:= hf i x fun t ht=> mitten a r i (arm D) hr (arm_pos _|>.le) ha hp x y t ht (by linarith) hy
         obtain ⟨p,hp',hP⟩:= arctic D x a i ha
         have hu: ε ≤ ε*(1+A)^K.card:= le_mul_of_one_le_right he.le (one_le_pow₀ (by linarith))
         have hJ:= h z (ε*(1+A)^K.card) p (he.trans_le hu) hp' (fun w=> ?_) H (fun v hm=>(hz' v hm).trans hu) 0 ⟨by linarith [arm_pos D],(arm_pos _).le⟩
         · simp [H0, chord,Ward.inc] at hJ; exact hJ.trans (by rw [pow_succ,← mul_assoc]; exact mul_le_mul_of_nonneg_left (by linarith) (he.trans_le hu).le)
         rw [H0]; refine ih (chord i x a (p w)) (fun j h'=> ?_) (?_)
         · by_cases he : j=i
           · subst j; exact hP w
           exact reed i j x a _ he (hh j (by simp [he,h']))
         have hj:= le_trans (rink (j:=i) (arm_pos _|>.le) x a ha (hp'.1 w)) hp
         linarith only [hj,hz,norm_sub_le_norm_sub_add_norm_sub (chord i x a (p w)) x y]
   have hl:= ht Finset.univ y (by simp) (?_)
   · simpa [Axis] using hl
   simp only [sub_self,norm_zero,Finset.card_univ,Axis,Fintype.card_fin,zero_add,Nat.cast_ofNat]; linarith
variable {G:Gauge}{C:Family G}
lemma read_grid {m:ℕ}{x:E4}(h:taper (C.S.a m) x= Set.univ):∃ i:Lattice.Cover,C.S.gridPoint m i=x∧ ∀ v:Axis,x v≠0:=by
   have hx (v:Axis):v∈ taper (C.S.a m) x:=by rw [h];trivial
   choose r hr hz using (show ∀ v:Axis,∃ i:ℤ, x v=C.S.a m*i∧ i≠0 from hx)
   refine ⟨r,?_,fun v=>?_⟩
   · ext i; exact (hr i).symm
   rw [hr]; exact mul_ne_zero (C.S.a_pos m|>.ne') (Int.cast_ne_zero.mpr (hz _))
set_option quotPrecheck false
local notation "R" => fun i:ℕ=> fuga C.path.levels (i+1)
lemma cloudW (I:Watch C)(hs: Note C.S (R) (-1)):∀ᶠ m in atTop, ∀ j:ℕ, ∀ y:Lattice.Cover, C.S.gridPoint j y∈arena ((R) m)→ (∀ v:Axis,C.S.gridPoint j y v≠0) → I.point j y∈generic _ :=by
    have hh:Tendsto (fun i=>4*(R) i) atTop (𝓝 0):=by simpa only [mul_zero] using (hs.thins (by norm_num)).const_mul (4:ℝ)
    have he (a:Axis)(j:Fin I.n):I.held j.succ a≠0:= fun h=> Fin.succ_ne_zero _ (I.wild a (show I.held j.succ a=I.held 0 a from by rw [I.origin,h];rfl))
    filter_upwards [eventually_all.mpr fun a=>eventually_all.mpr fun i=> hh.eventually (gt_mem_nhds (abs_pos.mpr (he a i)))] with m hm j y hy h
    refine avoid_cons I _ (fun a i=> Fin.cases (by rw [I.origin]; exact (h a).symm) (fun b=>?_ ) i)
    intro hh; have hv:=hm a b; rw [hh] at hv
    apply hv.not_ge; exact (show _ ≤ ‖C.S.gridPoint j y‖ from PiLp.norm_apply_le _ _).trans hy.2.le
end YM.MergeProof.Acme
