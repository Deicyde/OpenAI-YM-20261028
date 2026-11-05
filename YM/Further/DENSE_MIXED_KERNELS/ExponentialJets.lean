import YM.Further.DENSE_MIXED_KERNELS.Pitch
import YM.Work.B04

/-!
# Log-domain budget conversions, V left jets before mask

Use inside legitimate smooth real extensions. Constants in exponent are
allowed large/extensive; they **cancel** in the normalized density.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Further.DenseMixedKernels
open Function Finset Filter Lattice RG Wilson
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {n : Side} {k j : ℕ} {U : Config G n} {T M : ℝ} {P : Directions G n → Prop}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "I" => Directions G n

/-- Does not charge the value piece (use even in a log with potentially large offset). -/
structure Pulse (f : Config G n → E) (U : Config G n) (P : Directions G n → Prop) (k : ℕ) (T : ℝ) : Prop where
  smooth : Rests f k U
  bounds : ∀ l : List (Directions G n), l ≠ [] → l.length ≤ k → (∀ v∈l,P v) → ‖leftDerivs f l U‖ ≤ T^l.length

section Pulse
variable {f g : Config G n → E}
lemma Pulse.reduce (h : Pulse f U P k T) (hv : j≤k) : Pulse f U P j T :=
    ⟨h.smooth.reduce hv,fun l hl he => h.bounds l hl (he.trans hv)⟩
lemma Pulse.prefix (h : Pulse f U P (j+1) T) {a : I} (hv : P a) : Pitch (leftDerivs f [a]) U P j T T := by
  refine ⟨h.smooth.tilt le_rfl,fun l hl ht => ?_⟩
  rw [← append_left]
  simpa only [List.length_append,List.length_singleton,pow_succ'] using!
    h.bounds (l++[a]) (by simp) (by simp; omega) (fun i hi => by
      simp only [List.mem_append,List.mem_singleton] at hi; grind)
lemma Pulse.wrap (h : Pulse f U P k T) (ht : 0≤T) (hm : 1≤M) (hc : ‖f U‖ ≤ M) : Pitch f U P k M T := by
  refine ⟨h.smooth,fun l hl hv => ?_⟩
  rcases eq_or_ne l [] with he|he
  · subst l; simpa only [leftDerivs,List.length_nil,pow_zero,mul_one] using hc
  exact (h.bounds l he hl hv).trans (le_mul_of_one_le_left (pow_nonneg ht _) hm)
lemma Pitch.pulse (h : Pitch f U P k M T) (ht : 0≤T) (hM : 1≤M) : Pulse f U P k (M*T) := by
  refine ⟨h.smooth,fun l hl he hh => (h.bounds l he hh).trans ?_⟩
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (by
    nth_rw 1 [← pow_one M]
    apply pow_le_pow_right₀ hM; exact List.length_pos_iff.mpr hl) (by positivity)


end Pulse

variable {f : Config G n → ℝ}

private lemma cut (n j k : ℕ) (hj : j ≤ k) (B : ℝ) (hB : B ≤ n*((n:ℝ)^k*T)) (ht : 0 ≤ T) (h : 1 ≤ n) (hh : 0 ≤ B) :
    T*B^j ≤ ((n:ℝ)^k*T)^(j+1) := by
  rw [pow_succ]; apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh hB _) ht)
  rw [mul_pow]; have hv : (n:ℝ)^j ≤ (n:ℝ)^k := pow_le_pow_right₀ (by exact_mod_cast h) hj
  have H : 0 ≤ ((n:ℝ)^k*T)^j := by positivity
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv H) ht).trans_eq (by ring)

lemma Pulse.flare (hf : Pulse f U P k T) (ht : 0 ≤ T) : Pitch (fun x => Real.exp (f x)) U P k (Real.exp (f U)) (2^k*T) := by
  let D := 2^k*T
  have he : 0≤D := by unfold D; positivity
  have ht' : T ≤ D := le_mul_of_one_le_left ht (one_le_pow₀ (by norm_num))
  let g x := Real.exp (f x)
  have hh : Rests g k U := ContDiffAt.exp hf.smooth
  suffices h : ∀ j : ℕ,j≤k → Pitch g U P j (g U) D from h k le_rfl
  intro j hj
  induction j with
  | zero =>
    refine ⟨hh.reduce hj,fun l hl _ => ?_⟩
    cases l <;> simp_all [g,leftDerivs]
  | succ j ih =>
    have hc := ih (show j ≤ k by omega)
    refine ⟨hh.reduce hj,fun l hl he' => ?_⟩
    cases l using List.reverseRecOn with
    | nil => exact hc.bounds [] (by simp) (by simp)
    | append_singleton l a =>
      have hg : (leftDerivs g [a]) ∘ increment U =ᶠ[𝓝 0] (fun y => g y * leftDerivs f [a] y) ∘ increment U := by
        filter_upwards [rest_inside (hf.smooth.reduce hj)] with v hv
        have h := ((hv.has a).exp).deriv; simp only [zero_smul,increment_zero] at h; exact h
      have hl' : l.length ≤ j := by simpa only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] using hl
      rw [append_left,left_eq l hg,List.length_append,List.length_singleton]; refine ((Pitch.real_mul hc
        ((hf.reduce hj).prefix (a:=a) (he' a (by simp)))).bounds l hl' fun v hv => he' v (by simp [hv])).trans ?_
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (by
        simpa only [Nat.cast_ofNat] using cut (T:=T) 2 l.length k (by omega) (D+T) (by
          push_cast; change D+T ≤ 2*D; linarith) ht (by decide) (by positivity)) (Real.exp_pos _).le

/-- Invert a positive weight with relative bounds, not via a uniform bound
on its values in the chart. -/
lemma Pitch.reverse (hf : Pitch f U P k (f U) T) (ht : 0 ≤ T) (he : 0 < f U) : Pitch (fun x => (f x)⁻¹) U P k (f U)⁻¹
    (3^k*T) := by
  let g x := (f x)⁻¹
  let D := 3^k*T
  have hd : 0 ≤ D := by unfold D; positivity
  have hd' : T ≤ D := le_mul_of_one_le_left ht (one_le_pow₀ (by norm_num))
  have hh : Rests g k U := ContDiffAt.inv hf.smooth (by simpa only [comp_apply,increment_zero] using he.ne')
  suffices ∀ j : ℕ, j ≤ k → Pitch g U P j (g U) D from this k le_rfl
  intro j hj
  induction j with
  | zero =>
    refine ⟨hh.reduce hj,fun l hl hD => ?_⟩
    cases l <;> simp_all [g,leftDerivs, abs_of_pos he]
  | succ j ih =>
    have hc := ih (show j≤k by omega)
    refine ⟨hh.reduce hj,fun l hl hD => ?_⟩
    cases l using List.reverseRecOn with
    | nil => exact hc.bounds [] (by simp) hD
    | append_singleton l a =>
      have hE : ∀ᶠ v in 𝓝 (0:I), (f ∘ increment U) v ≠ 0 :=
        ContDiffAt.continuousAt hf.smooth |>.eventually_ne (by simpa only [comp_apply,increment_zero] using he.ne')
      have hg : (leftDerivs g [a]) ∘ increment U =ᶠ[𝓝 0] (fun y => -(g y * g y * leftDerivs f [a] y)) ∘ increment U := by
        filter_upwards [hE,rest_inside (hf.smooth.reduce hj)] with v hv hw
        let V := increment U v
        have h' := ((hw.has a).inv (by rw [zero_smul,increment_zero]; exact hv)).deriv
        simp only [zero_smul,increment_zero] at h'
        change leftDerivs g [a] V = _
        apply h'.trans; unfold g; simp only [comp_apply]; ring
      have H := (Pitch.real_mul (Pitch.real_mul hc hc) ((hf.under hj).tilt (a:=a) (hD _ (by simp)))).negate
      have hl' : l.length ≤ j := by simpa only [List.length_append,List.length_singleton,Nat.add_le_add_iff_right] using hl
      rw [append_left,left_eq l hg,List.length_append,List.length_singleton]
      refine (H.bounds l hl' fun v hv => hD v (by simp [hv])).trans ?_
      rw [show g U*g U*(f U*T)=g U*T by unfold g; field_simp,mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (show 0≤g U from inv_nonneg.mpr he.le)
      simpa only [Nat.cast_ofNat] using cut (T:=T) 3 l.length k (by omega) (D+D+T) (by
        push_cast; change D+D+T ≤ 3*D; linarith) ht (by decide) (by positivity)

end YM.Further.DenseMixedKernels
