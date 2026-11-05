import YM.Further.DENSE_MIXED_KERNELS.ExponentialJets

/-!
# Positive-order composition, on ordered V jets

A finite-dimensional projector/primitive oracle can supply jets of curves
into group expressions etc. Don't budget value of a whole HAAR product even
when we are extracting change in slopes; otherwise repeated evaluation
costs can consume all weight. Here pay ordinary positive derivatives.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Filter Function Finset MeasureTheory Lattice RG Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {k j : ℕ} {U : Config G n} {M C t T : ℝ} {P : Directions G n → Prop}
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f m : Config G n → E} {g : E → F}

structure Ripple (f : Config G n → E) (U : Config G n) (P : Directions G n → Prop) (k : ℕ) (M T : ℝ) : Prop where
  smooth : Rests f k U
  each : ∀ l : List (Directions G n), l ≠ [] → l.length ≤ k → (∀ v∈l,P v) → ‖leftDerivs f l U‖ ≤ M*T^l.length

namespace Ripple
lemma trim (h : Ripple f U P k M T) (hs : j≤k) : Ripple f U P j M T :=
  ⟨h.smooth.reduce hs,fun l he hl => h.each l he (hl.trans hs)⟩
lemma front (h : Ripple f U P (k+1) M T) {a : Directions G n} (ha : P a) : Pitch (leftDerivs f [a]) U P k (M*T) T := by
  refine ⟨h.smooth.tilt le_rfl,fun l hl hh => ?_⟩
  have he v (hv : v∈l ++ [a]) : P v := by
    rcases List.mem_append.mp hv with hx|hx; exact hh v hx; rw [List.mem_singleton.mp hx]; exact ha
  simpa only [append_left,List.length_append,List.length_singleton, pow_succ',mul_assoc] using!
    h.each (l++[a]) (by simp) (by simpa using hl) he

lemma parcel (h : Ripple f U P k M T) (ht : 0≤T) (he : M ≤ C) (hf : ‖f U‖ ≤ C) : Pitch f U P k C T := by
  refine ⟨h.smooth,fun l hl hv => ?_⟩
  rcases eq_or_ne l [] with h'|h'; subst l; simpa only [leftDerivs,List.length_nil,pow_zero,mul_one]
  exact (h.each l h' hl hv).trans (mul_le_mul_of_nonneg_right he (pow_nonneg ht _))
lemma mono (h : Ripple f U P k M t) (ht : 0≤t) (hp : t≤T) (hC : 0≤C) (hc : M ≤ C) : Ripple f U P k C T :=
  ⟨h.smooth, fun l hl he hh => (h.each l hl he hh).trans (mul_le_mul hc (pow_le_pow_left₀ ht hp _)
    (pow_nonneg ht _) hC)⟩
lemma save (h : Ripple f U P k (C*M) T) (ht : 0≤T) (hC : 1≤C) (hp : 0≤M) : Ripple f U P k M (C*T) := by
  refine ⟨h.smooth,fun l hl he hh => ?_⟩
  apply (h.each l hl he hh).trans; rw [mul_comm C,mul_pow,←mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht _)
  exact mul_le_mul_of_nonneg_left (by nth_rw 1 [← pow_one C]; exact pow_le_pow_right₀ hC (List.length_pos_iff.mpr hl)) hp
lemma unit (h : Ripple f U P k 1 T) : Pulse f U P k T := ⟨h.smooth,fun l hl he hh => by simpa using h.each l hl he hh⟩

/-- M is a small prefactor at *each positive* order, not T itself small.
At k higher than one don't replace by a hypothesis that M^k is available. -/
theorem comp (h : Ripple f U P k M T) (hM : M≤1) (hy : 0≤T) (hc : 0≤C) (hg : ContDiffAt ℝ k g (f U))
    (hh : ∀ j, 0<j → j≤k → ‖iteratedFDeriv ℝ j g (f U)‖ ≤ C) (hm : 0 ≤ M) : Ripple (g∘f) U P k (C*M) (2^k*T) := by
  let r := 2^k*T
  have hr : 0 ≤ r := by unfold r; positivity
  have hv : T ≤ r := le_mul_of_one_le_left hy (one_le_pow₀ (by norm_num))
  suffices He : ∀ j : ℕ,j≤k → ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : E → F),
      ContDiffAt ℝ j g (f U) → (∀ i, 0 < i → i≤j → ‖iteratedFDeriv ℝ i g (f U)‖ ≤ C) → Ripple (g∘f) U P j (C*M) r by
    exact He k le_rfl g hg hh
  intro j hj
  induction j with
  | zero =>
    intro F _ _ p H hp
    have hv : increment U 0=U := increment_zero U
    refine ⟨ContDiffAt.comp (f:=f∘increment U) _ (g:=p) (by simpa only [comp_apply,hv] using H) (h.smooth.reduce hj),fun l hl he => ?_⟩
    cases l <;> simp_all
  | succ j ih =>
    intro F _ _ p H hp
    have hf := h.trim hj
    let k' (y : E) := fderiv ℝ p y
    have hh : ContDiffAt ℝ j k' (f U) := H.fderiv_right (by simp)
    have he i (hi : i≤j) : ‖iteratedFDeriv ℝ i k' (f U)‖ ≤ C := by
      simpa only [iteratedFDeriv_succ_eq_comp_right,comp_apply, LinearIsometryEquiv.norm_map] using!
        hp (i+1) (by omega) (by omega)
    have hD := ih (show j≤k by omega) k' hh fun i _ hi => he i hi
    have hq : Pitch (k'∘f) U P j C r := hD.parcel hr (mul_le_of_le_one_right hc hM)
      (by simpa only [norm_iteratedFDeriv_zero,comp_apply] using he 0 (Nat.zero_le _))
    refine ⟨ContDiffAt.comp (f:=f∘increment U) _ (g:=p) (by rw [comp_apply,increment_zero]; exact H)
      hf.smooth, fun l hl he' hA => ?_⟩
    cases l using List.reverseRecOn with
    | nil => tauto
    | append_singleton l a =>
      have hA' (v) (hv : v∈l) := hA v (by simp [hv])
      have hj' : l.length ≤ j := by simpa only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] using he'
      have ht := Pitch.clm (g:=leftDerivs f [a]) hq (hf.front (hA a (by simp)))
      have hd : (leftDerivs (p∘f) [a]) ∘ increment U =ᶠ[𝓝 0]
          (fun v => fderiv ℝ p (f v) (leftDerivs f [a] v)) ∘ increment U := by
        filter_upwards [rest_inside hf.smooth,
          (show Tendsto (f ∘ increment U) (𝓝 0) (𝓝 (f U)) from by
            simpa only [ContinuousAt,comp_apply,increment_zero] using! ContDiffAt.continuousAt hf.smooth).eventually
          (H.eventually (by simp))] with v hz hx
        let V := increment U v
        have he : HasFDerivAt p (fderiv ℝ p (f V)) (f (increment V ((0:ℝ) • a))) := by
          rw [zero_smul, increment_zero]; exact (hx.differentiableAt (by simp)).hasFDerivAt
        exact (he.comp_hasDerivAt 0 (hz.has a)).deriv
      rw [append_left,left_eq l hd,List.length_append,List.length_singleton]; refine (ht.bounds l hj' hA').trans ?_
      rw [← mul_assoc, mul_assoc (C*M)]
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc hm)
      calc
        _ ≤ T*(2*r)^l.length := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) hy
        _ = (2^l.length*T)*r^l.length := by rw [mul_pow]; ring
        _ ≤ r*r^l.length := by exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
          (show l.length ≤ k by omega)) hy) (by positivity)
        _ = _ := (pow_succ' ..).symm

lemma neg (h : Ripple f U P k M T) : Ripple (fun x => -f x) U P k M T :=
    ⟨h.smooth.neg, fun _ hl he hh => by rw [negate_left,norm_neg]; exact h.each _ hl he hh⟩
lemma plus (h : Ripple f U P k M T) (hh : Ripple m U P k C T) : Ripple (fun x => f x+m x) U P k (M+C) T :=
    ⟨h.smooth.plus hh.smooth, fun l hl he hA => by
      rw [plus_left h.smooth hh.smooth l he,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.each _ hl he hA) (hh.each _ hl he hA))⟩
lemma linear (h : Ripple f U P k M T) (L : E→L[ℝ]F) {D : ℝ} (he : ∀ x,‖L x‖≤D*‖x‖) (hd : 0≤D) :
    Ripple (fun x => L (f x)) U P k (D*M) T := by
  refine ⟨L.contDiff.contDiffAt.comp _ h.smooth, fun l hl hy hv => ?_⟩
  rw [clm_left _ h.smooth l hy,mul_assoc]; exact (he _).trans (mul_le_mul_of_nonneg_left (h.each _ hl hy hv) hd)
lemma onLeft (h : Ripple f U P k M T) (L : E→L[ℝ]F) (he : ∀ x,‖L x‖ ≤ ‖x‖) : Ripple (fun x => L (f x)) U P k M T := by
  simpa only [one_mul] using h.linear L (D:=1) (fun i => by simpa using he i) zero_le_one
lemma equiv (h : Ripple f U P k M T) (he : m ∘ increment U =ᶠ[𝓝 0] f ∘ increment U) : Ripple m U P k M T :=
    ⟨ContDiffAt.congr_of_eventuallyEq h.smooth he,fun l hl hy hh => by rw [left_eq l he]; exact h.each _ hl hy hh⟩
lemma fixed (M T : ℝ) (hm : 0≤M) (ht : 0≤T) (v : E) : Ripple (fun _ => v) U P k M T := by
  have h l (x : Config G n) : leftDerivs (fun _=>v) l x= if l=[] then v else 0 := by
    induction l generalizing x with | nil => simp [leftDerivs] | cons A l ih => simp only [leftDerivs,ih,List.cons_ne_nil,↓reduceIte,deriv_const]
  exact ⟨contDiffAt_const, fun l hl he hh => by rw [h,if_neg hl,norm_zero]; positivity⟩
lemma pi {ι : Type} [Fintype ι] {f : Config G n → (ι→E)} (ht : 0≤T) (hM : 0≤M)
    (h : ∀ i:ι,Ripple (fun x=> f x i) U P k M T) : Ripple f U P k M T := by
  have he : Rests f k U := contDiffAt_pi.mpr fun i => (h i).smooth
  refine ⟨he,fun l hl hv hp => (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)⟩
  exact (show leftDerivs (fun x => f x i) l U = leftDerivs f l U i from (clm_left (ContinuousLinearMap.proj (R:=ℝ) i) he l hv)) ▸ (h i).each l hl hv hp
lemma pair {h : Config G n → F} (he : Ripple f U P k M T) (hh : Ripple h U P k M T) :
    Ripple (fun x => (f x,h x)) U P k M T := by
  let g x := (f x,h x); have hf : Rests g k U := ContDiffAt.prodMk he.smooth hh.smooth
  refine ⟨hf,fun l hl he' hh' => ?_⟩
  change ‖leftDerivs g l U‖ ≤ _
  rw [Prod.norm_def,← show leftDerivs f l U=(leftDerivs g l U).1 from (clm_left (ContinuousLinearMap.fst ℝ E F) hf l he'),
    ← show leftDerivs h l U=(leftDerivs g l U).2 from (clm_left (ContinuousLinearMap.snd ℝ E F) hf l he')]
  exact max_le (he.each l hl he' hh') (hh.each l hl he' hh')
end Ripple
end YM.Further.DenseMixedKernels
