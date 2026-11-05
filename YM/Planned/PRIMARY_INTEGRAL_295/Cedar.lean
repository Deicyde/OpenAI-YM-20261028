import YM.Planned.PRIMARY_INTEGRAL_295.Dials



/-!
# Polynomial path costs for Principal windows of AFFINE Gram

Power profiles in THIS principal component can pay poly in local volume
(post-L before weak realization). Avoid assumptions smooth on far
selected branches. No receipts for long chains or forced volumes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Cedar
open Function Filter Set Metric MeasureTheory ProbabilityTheory
open Labels Lattice RG Wilson Source Source.Drops Oval Precision Exterior Tree Streets Porous Carrier Bloch
  
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {E F A B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {n k : ℕ} {C D : ℝ}

abbrev Ember (n:ℕ) (f:E→F) (c:ℝ) := ContDiffAt ℝ n f 0 ∧ Envelope 0 n f c
namespace Ember
variable {f g : E→F} (h : Ember n f C)
include h
lemma down (hd:k≤n) : Ember k f C:=⟨h.1.of_le (Nat.cast_le.mpr hd), h.2.1,fun i hi=>h.2.2 i (hi.trans hd)⟩
lemma join (hf:Ember n g D) : Ember n (f+g) (C+D):= ⟨h.1.add hf.1,Seas.add h.1 hf.1 h.2 hf.2⟩
lemma flipped : Ember n (-f) C:= ⟨h.1.neg,h.2.1,fun i hi=>by rw [iteratedFDeriv_neg_apply,norm_neg]; exact h.2.2 i hi⟩
lemma erase (hf:Ember n g D) : Ember n (f-g) (C+D):= by rw [sub_eq_add_neg]; exact join h (flipped hf)
lemma weakening (hd : C≤D) : Ember n f D:= ⟨h.1,Seas.less h.2 hd⟩
lemma renamed (he:g =ᶠ[𝓝 0] f) : Ember n g C:= by refine ⟨h.1.congr_of_eventuallyEq he,h.2.1,fun b hb=>?_⟩; rw [(he.iteratedFDeriv ℝ _).self_of_nhds]; exact h.2.2 _ hb
lemma scaled (c:ℝ) : Ember n (c • f) (‖c‖*C) := ⟨h.1.const_smul c,Seas.scaleBy h.1 c C h.2⟩
omit h
lemma constant (C:F) (n:ℕ): Ember n (fun _ : E=>C) ‖C‖:=⟨contDiffAt_const,norm_nonneg _,fun i _=>by
     by_cases h:i=0
     · subst i; rw [norm_iteratedFDeriv_zero]
     rw [iteratedFDeriv_const_of_ne h]; simp⟩
lemma neutral (n : ℕ) : Ember n (0:E→F) 0:= by
     have he:Ember n (0:E→F) ‖(0:F)‖:=constant (0:F) n; rwa [norm_zero] at he

lemma total (s: Finset A) (c:A→ℝ) (f:A→E→F) (h:∀ i∈s, Ember n (f i) (c i)):
    Ember n (fun y=>∑ i∈s,f i y) (∑ i∈s,c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact neutral n
  | insert i s hi ih =>
    have he:= h i (by simp)
    simp_rw [Finset.sum_insert hi]; exact join he (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

lemma cumul [Fintype A] (f:A→E→F) (h:∀ i, Ember n (f i) C): Ember n (fun y=>∑ i, f i y) ((Fintype.card A:ℝ)*C) := by
   have ht:=total Finset.univ (fun _:A=>C) f (fun i _=> h i)
   rwa [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht

variable {H : Type*} [NormedRing H] [NormedAlgebra ℝ H]
private lemma combs {f g:E→H} {a:ℕ} (hp:ContDiffAt ℝ a f 0) (hq:ContDiffAt ℝ a g 0) (hd:0≤D) (hc:0≤C)
    (hfg:∀ i, i≤a→ ‖iteratedFDeriv ℝ i f 0‖ * ‖iteratedFDeriv ℝ (a-i) g 0‖ ≤ C*D) (ha:a≤k) :
    ‖iteratedFDeriv ℝ a (fun y=> f y*g y) 0‖ ≤ 2^k*(C*D) := by
    refine (Kelps.product_at 0 hp hq).trans ?_
    have hs i (hi : i∈ Finset.range (a+1)): (a.choose i : ℝ)*‖iteratedFDeriv ℝ i f 0‖ * ‖iteratedFDeriv ℝ (a-i) g 0‖≤
        (a.choose i:ℝ)*(C*D):=by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hfg i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))) (by positivity)
    have he : (∑ i∈ Finset.range (a+1), (a.choose i:ℝ)) = 2^a := by simpa [show (1+1:ℝ)=2 by norm_num] using (add_pow (1:ℝ) 1 a).symm
    refine (Finset.sum_le_sum hs).trans ?_; rw [←Finset.sum_mul,he]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) ha) (by positivity)

lemma fires {f g:E→H} (hf : Ember n f C) (hg : Ember n g D) : Ember n (fun y=> f y*g y) (2^n*(C*D)):= by
    have hp:=hf.2.1; have hq:=hg.2.1; refine ⟨hf.1.mul hg.1,by positivity, fun i hi=>?_⟩
    exact combs (down hf hi).1 (down hg hi).1 hq hp (fun j hj=>mul_le_mul (hf.2.2 j (hj.trans hi))
        (hg.2.2 _ ((Nat.sub_le ..).trans hi)) (norm_nonneg _) hp) hi

lemma reduced {f g:E→H} (ht:f 0=0) (hf : Ember (n+1) f C) (hg:ContDiffAt ℝ (n+1:ℕ) g 0) (hx : Envelope 0 n g D):
      Ember (n+1) (fun y=> f y*g y) (2^(n+1)*(C*D)):= by
    have hp:=hf.2.1; have hq:=hx.1; refine ⟨hf.1.mul hg,by positivity, fun i hi=>?_⟩
    refine combs (down hf hi).1 (hg.of_le (Nat.cast_le.mpr hi)) hq hp (fun j hj=>?_) hi
    by_cases hy:j=0
    · rw [hy,norm_iteratedFDeriv_zero,ht,norm_zero,zero_mul]; positivity
    exact mul_le_mul (hf.2.2 j (hj.trans hi)) (hx.2 _ (by omega)) (norm_nonneg _) hp
end Ember

end YM.Planned.PrimaryIntegral295.Cedar
