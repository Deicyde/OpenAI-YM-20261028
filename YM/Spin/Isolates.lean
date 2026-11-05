import Mathlib.Analysis.CStarAlgebra.Projection




/-!
# Perturb a **non-normal** almost-idempotent to an idempotent, centrally

For avoiding a full Lie integration theorem in the rotations step: correct
spectral projection for Casimir free rep persists.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Spin
open Filter Function Metric Set
open scoped Topology BigOperators
variable {R : Type*} [NormedRing R]

def defect (x : R) := x^2-x
def φ (x : R) := 3*x^2-2*x^3
lemma offset (x : R) : φ x-x=(1-2*x)*defect x := by unfold φ defect; noncomm_ring
lemma demand (x : R) : defect (φ x)=(4*defect x-3)*defect x^2 := by unfold φ defect; noncomm_ring

variable [CompleteSpace R]
lemma rectify (A C ε : ℝ) (hC : ‖(1:R)‖ + ‖(2:R)‖*A < C) (x : R) (hx : ‖x‖ + C * (ε*2) ≤ A)
    (he : ‖defect x‖ ≤ ε) (hh : (‖(4:R)‖ * ε + ‖(3:R)‖) * ε ≤ 1/2) (hc : 0<C) :
    ∃ y : R, Tendsto (fun n : ℕ => φ^[n] x) atTop (𝓝 y) ∧ defect y=0 ∧ ‖y-x‖ ≤ C * (ε*2) := by
  let θ := (1:ℝ)/2
  have h : 0 ≤ ε := (norm_nonneg _).trans he
  let f (i : ℕ) := φ^[i] x
  have hθ : 0 < θ := by norm_num [θ]
  have ht i : f (i+1)=φ (f i) := iterate_succ_apply' ..
  let s (i : ℕ) := ε*θ^i
  have hs i : 0 ≤ s i := by unfold s; positivity
  have hb (i : ℕ) (hi : ‖defect (f i)‖ ≤ s i) (hy : ‖f i-x‖ ≤ C*(ε-s i)*2) :
      dist (f (i+1)) (f i) ≤ C * s i := by
    have hl : ‖f i‖ ≤ A := by
      calc ‖f i‖ ≤ ‖f i-x‖ + ‖x‖ := by nth_rw 1 [← sub_add_cancel (f i) x]; exact norm_add_le ..
           _ ≤ C*ε*2+‖x‖ := add_le_add_left (hy.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
               (sub_le_self _ (hs i)) hc.le) (by norm_num))) _
           _ ≤ A := by linarith
    rw [dist_eq_norm,ht,offset]; apply (norm_mul_le _ _).trans (mul_le_mul (?_ : ‖1-2*f i‖ ≤ C) hi (norm_nonneg _) hc.le)
    apply (norm_sub_le ..).trans _
    linarith [le_trans (norm_mul_le (2:R) (f i)) (mul_le_mul_of_nonneg_left hl (norm_nonneg (2:R)))]
  have hv i : ‖defect (f i)‖ ≤ s i ∧ ‖f i-x‖ ≤ C*(ε-s i)*2 := by
    induction i with
    | zero => simpa [f,s] using he
    | succ i ih =>
      have ha : s i ≤ ε := mul_le_of_le_one_right h (pow_le_one₀ hθ.le (by norm_num [θ]))
      have hz : s (i+1)=s i/2 := by simp only [s,pow_succ,θ]; ring
      constructor
      · rw [ht,demand,hz];
        have Ht : ‖4*(defect (f i))-3‖ ≤ ‖(4:R)‖*ε+‖(3:R)‖ := (norm_sub_le ..).trans
          (add_le_add_left ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (ih.1.trans ha) (norm_nonneg _))) _)
        apply le_trans ((norm_mul_le ..).trans (mul_le_mul Ht (le_trans (show ‖defect (f i)^2‖ ≤ ‖defect (f i)‖^2 by simp only [pow_two]; exact norm_mul_le _ _) (pow_le_pow_left₀
          (norm_nonneg (defect (f i))) ih.1 2)) (norm_nonneg _) ((norm_nonneg _).trans Ht)))
        have he := le_trans (mul_le_mul_of_nonneg_left ha (show 0 ≤ _*ε + ‖(3:R)‖ from by positivity)) hh
        nlinarith [hs i]
      calc _ = dist (f (i+1)) x := (dist_eq_norm _ _).symm
           _ ≤ dist (f (i+1)) (f i)+dist (f i) x := dist_triangle ..
           _ ≤ _ := by rw [hz]; have hh := hb i ih.1 ih.2; rw [dist_eq_norm (f i) x]; linarith [ih.2]
  have hΘ : θ < 1 := by norm_num [θ]
  obtain ⟨y,hy⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric θ (C*ε) hΘ (fun i => show dist (f i) (f (i+1)) ≤ _ by
    rw [dist_comm,mul_assoc]; exact hb _ (hv i).1 (hv i).2))
  have he : Tendsto s atTop (𝓝 0) := by simpa only [mul_zero] using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le hΘ).const_mul ε
  refine ⟨y,hy, norm_eq_zero.mp ?_,?_⟩
  · exact tendsto_nhds_unique ((hy.pow 2 |>.sub hy).norm) (squeeze_zero (fun i => norm_nonneg _) (fun i => (hv i).1) he)
  rw [← mul_assoc]
  exact le_of_tendsto_of_tendsto' ((hy.sub_const x).norm) (show Tendsto (fun i => C*(ε-s i)*2) atTop (𝓝 (C*ε*2)) by simpa only [sub_zero] using ((he.const_sub ε).const_mul C).mul_const (2:ℝ)) (fun i => (hv i).2)


lemma stable {z : R} (hz : defect z=0) (Z : ℕ → R) (ht : Tendsto Z atTop (𝓝 z)) : ∃ P : ℕ → R,
    (∀ᶠ n in atTop, Tendsto (fun i : ℕ => φ^[i] (Z n)) atTop (𝓝 (P n)) ∧ defect (P n)=0) ∧ Tendsto P atTop (𝓝 z) := by
  let A := ‖z‖+1
  obtain ⟨C,hC⟩ := exists_gt (‖(1:R)‖+‖(2:R)‖*A)
  have hc : 0 < C := by
    have hv : 0<A := by dsimp only [A]; positivity
    exact lt_of_le_of_lt (by positivity) hC
  let E n := ‖defect (Z n)‖
  have he : Tendsto E atTop (𝓝 0) := by
    have hv := (ht.pow 2 |>.sub ht).norm
    rw [show z^2-z=0 from hz,norm_zero] at hv; exact hv
  have hh : Tendsto (fun i => C*(E i*2)) atTop (𝓝 0) := by simpa using ((he.mul_const (2:ℝ)).const_mul C)
  have hy : ∀ᶠ i in atTop, ‖Z i‖+C*(E i*2) ≤ A := by
    apply ((ht.norm.add hh).eventually (gt_mem_nhds (?_ : ‖z‖+0 < A))).mono (fun i hi => show _ from le_of_lt hi)
    dsimp only [A]; linarith
  have hp := (he.const_mul ‖(4:R)‖ |>.add_const ‖(3:R)‖ |>.mul he)
  simp only [mul_zero,zero_add] at hp
  let e (p : ℕ) (y : R) := Tendsto (fun i : ℕ => φ^[i] (Z p)) atTop (𝓝 y) ∧ defect y=0 ∧ ‖y-Z p‖ ≤ C*(E p*2)
  have hE : ∀ᶠ i in atTop, ∃ y, e i y := (hy.and (hp.eventually (gt_mem_nhds
    (by norm_num : (0:ℝ)<1/2)))).mono (fun i hi => rectify A C (E i) hC _ hi.1 le_rfl (le_of_lt hi.2) hc)
  classical
  let P (n : ℕ) := if h : ∃ y, e n y then h.choose else z
  replace hE : ∀ᶠ i in atTop,e i (P i) := hE.mono fun i hi => by dsimp only [P]; rw [dif_pos hi];exact hi.choose_spec
  refine ⟨P,hE.mono (fun i hi => ⟨hi.1,hi.2.1⟩),?_⟩
  have hv : Tendsto (fun i => P i-Z i) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) (hE.mono fun i hi => hi.2.2) hh)
  simpa using hv.add ht
end YM.Spin
