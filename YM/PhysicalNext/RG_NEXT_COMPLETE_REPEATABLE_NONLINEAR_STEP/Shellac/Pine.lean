import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment
import YM.Planned.STATIONARY_JET_PORT.AtHome
/-!
# Dynamics of subtracting a V-independent value and recovering ε-affine from measured equations
 All at Euclidean auxiliary. Mirror no linear. Need normalized gust for Lens radial read.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Shellac
open Function Filter Set Metric Lattice MeasureTheory Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented   Bid Planned.JetPort
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums   
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {u f : E→F} {k j n : ℕ} {a b s C r p : ℝ}

def off (u : E→F) := u-fun _=>u 0
lemma drips {x:E} (h : Brush n a b f x) : ∀ k, k≤n → 0<k → normJ k (off f) x ≤ a*b^k:= by
  intro k hk hv; obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero hv.ne'
  unfold normJ off; rw [iteratedFDeriv_sub_apply (h.smaller hk).smooth contDiffAt_const,iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]; exact h.order _ hk
lemma pools (ha:0<a) (he:a≤1) (h:k≤n) (hq:0 ≤ C) (hb : 0 ≤ b) (hp: ∀ y∈ ball 0 a,ContDiffAt ℝ n f y)
    (hg : ∀ i, k ≤ i → i≤n →∀ y∈ball 0 a,normJ i f y ≤ C) (h₀: ∀ i:ℕ,i<k→ normJ i f 0*a^i ≤ b) :
    ∀ y∈ball 0 a,Brush n (C*a^k + (k:ℝ)*b) a⁻¹ f y:= by
  have ht : ∀ i:ℕ, ∀ (hi:i ≤ k), ∀ y∈ball 0 a,normJ i f y * a^i ≤ C*a^k + (k-i:ℕ)*b:= by
    intro i hi; induction hi using Nat.decreasingInduction with
    | self=> intro y hy; rw [Nat.sub_self, Nat.cast_zero,zero_mul,add_zero]; exact mul_le_mul_of_nonneg_right (hg k le_rfl h _ hy) (pow_nonneg ha.le _)
    | of_succ i hi ih=>
      intro x hx
      have hy:ContDiffAt ℝ (↑(i+1:ℕ)) f x:=(hp x hx).of_le (Nat.cast_le.mpr (hi.trans_le h)) -- i+1 indeed Nat.lt def use hi + not strict sense
      let w:= iteratedFDeriv ℝ i f
      let m:=C*a^k+ ((k-(i+1):ℕ):ℝ)*b
      have hm : 0 ≤ m:=by unfold m; positivity
      have hV : ‖w x-w 0‖ ≤ m/a^(i+1)*a:= by
        have ht:= (convex_ball (0:E) a).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (C:=m/a^(i+1))
          (f:=w) (fun y hy=>((hp y hy).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr (hi.trans_le h)))) (fun y hy=>?_) (mem_ball_self ha) hx
        · rw [sub_zero] at ht; exact ht.trans (mul_le_mul_of_nonneg_left (mem_ball_zero_iff.mp hx).le (by positivity))
        rw [show ‖fderiv ℝ w y‖=_ from norm_fderiv_iteratedFDeriv]; exact (le_div_iff₀ (by positivity)).mpr (ih _ hy)
      have hv : k-i=k-(i+1)+1:=by omega
      change ‖w x‖ * a^i ≤ _
      calc _ ≤ (‖w x-w 0‖+ ‖w 0‖) * a^i := mul_le_mul_of_nonneg_right (by rw [add_comm]; exact norm_le_insert' _ _) (by positivity)
           _ ≤ _ := by rw [add_mul,hv]; push_cast; apply le_trans (add_le_add (mul_le_mul_of_nonneg_right hV (by positivity)) (h₀ i hi)); apply le_of_eq; field_simp; unfold m; ring
  intro y hy; refine ⟨hp y hy,(inv_pos.mpr ha).le,fun i hi=>?_⟩
  rw [inv_pow,← div_eq_mul_inv]; apply (le_div_iff₀ (pow_pos ha i)).mpr
  rcases le_total i k with he'|he'
  · refine (ht i he' y hy).trans ?_; gcongr; exact Nat.sub_le ..
  exact (mul_le_mul (hg i he' hi y hy) (pow_le_pow_of_le_one ha.le he he') (pow_nonneg ha.le _) hq).trans (le_add_of_nonneg_right (by positivity))
lemma rapid {x : E} (h : ∀ i∈closedBall (0:E) ‖x‖, Brush n C 1 u i) (hx : ‖x‖ ≤ s) (hi:1≤n) (he : 0 < s) (hs : s≤1): Brush n (C*s) s⁻¹ (off u) x := by
  let m:= ‖x‖; let X:= closedBall (0:E) m; have hf :=mem_closedBall_self (x:=(0:E)) (norm_nonneg x)
  have hV:x∈X := mem_closedBall_zero_iff.mpr le_rfl; have hK:= h x hV
  have hg:= hK.smaller hi; have hC:= hg.nonneg
  have hB : ‖u x-u 0‖ ≤ C*s := by
    have hv:= (convex_closedBall (0:E) m).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=u) (fun i hi'=>(((h i hi').smaller hi).smooth.differentiableAt (by norm_num))) (C:=C) (fun i hi'=> by rw [←norm_iteratedFDeriv_one]; exact (Brush.offer.1 (h i hi')).2 1 hi) hf hV
    rw [sub_zero] at hv; exact hv.trans (mul_le_mul_of_nonneg_left hx hC)
  refine ⟨hK.smooth.sub contDiffAt_const,(inv_pos.mpr he).le,fun j hj=>?_⟩
  rcases j with _|j
  · rw [normJ,norm_iteratedFDeriv_zero,pow_zero,mul_one]; exact hB
  have he' := drips hK (j+1) hj (Nat.succ_pos _); rw [one_pow,mul_one] at he'
  refine he'.trans ?_; rw [pow_succ',mul_assoc, ← mul_assoc s, mul_inv_cancel₀ he.ne', one_mul]; exact le_mul_of_one_le_right hC (one_le_pow₀ (one_le_inv₀ he|>.2 hs))
end YM.PhysicalNext.Repeat.Shellac
