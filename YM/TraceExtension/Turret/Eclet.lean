import YM.TraceExtension.Turret.Hose
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open WardBin Filch
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {X Y: Type}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup Y][NormedSpace ℝ Y]
variable {n m k:ℕ}{A C t s u:ℝ}{f:X→Y}
-- large small-field curve jets. May keep mask outside.
lemma hop (h:0 ≤ s) (hp:(∀ x:X, ‖x‖ ≤  s→ ContDiffAt ℝ ω f x)) (hx : ∀ i, i ≤ n → ∀ x:X, ‖x‖ ≤ s→ ‖iteratedFDeriv ℝ i f x‖ ≤  C)(ht:0 ≤  C): ∀ i,i ≤ n →∀ x:X,‖x‖ ≤ s→Allows n f x C := fun _ _ x h=> ⟨hp _ h,fun i he=> hx i he x h⟩
def evenR(d:ℕ)(K:ℝ):ℝ:= (1+K)^d
-- input scaled τ; function analytic originally. top j+a bound on raw.L. use d offset. retain normalized costs. arbitrary n,Y. explicit recursion.
lemma haloA (d:ℕ)(R:ℝ)(ht:0  ≤  R)(hs:0  ≤  s)(h:∀ x:X,‖x‖ ≤ R*s→Allows (k+d) f x C) (hC:0 ≤  C)(hh:∀ i:ℕ,k ≤ i→i<k+d→‖iteratedFDeriv ℝ i f 0‖ ≤  C*s^(k+d-i)) :∀ x, ‖x‖ ≤  R*s→ ‖iteratedFDeriv ℝ k f x‖  ≤  C * evenR d R*s^d :=by
    induction d generalizing k with
    | zero=> intro x hx; simpa[evenR] using (h x hx).norm_le k (by omega)
    | succ d ih=>
      intro x hx
      have hr : k+1+d=k+(d+1):=by omega
      have hk:= ih (k:=k+1) (by rw[hr]; exact h) (fun i he he'=> by rw[hr]; apply hh <;> omega)
      let Q:=evenR d R; have hQ:1 ≤  Q:=one_le_pow₀ (le_add_of_nonneg_right ht)
      let T:=iteratedFDeriv ℝ k f; let S:=Metric.closedBall (0:X) (R*s); have h0:(0:X)∈S:= Metric.mem_closedBall_self (by positivity)
      have hv(y:X):y∈S ↔ ‖y‖ ≤  R*s:=by simp[S]
      have hu:= Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (s:=S) (f:=T) (C:=C*Q*s^d) (fun y hy=> (h y ((hv _).mp hy)|>.analytic).differentiableAt_iteratedFDeriv (by simp)) (fun y hy=> (fare_lefter X Y f k y).trans_le (hk y ((hv _).mp hy))) (convex_closedBall ..) h0 ((hv _).mpr hx)
      rw[sub_zero] at hu; have hz:‖T 0‖  ≤  C*s^(d+1):= le_trans (hh k le_rfl (by omega)) (le_of_eq (by rw[show k+(d+1)-k=d+1 by omega]))
      have hi:= add_le_add (hu.trans (mul_le_mul_of_nonneg_left hx (show 0 ≤  C*Q*s^d by positivity))) hz
      have he : ‖T x‖  ≤  ‖T x-T 0‖+‖T 0‖:=by simpa only [sub_add_cancel] using norm_add_le (T x-T 0) (T 0)
      refine (he.trans hi).trans ?_; have hv : C*s^(d+1)  ≤  C*Q*s^(d+1):=mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hQ) (by positivity)
      apply le_trans (add_le_add_right hv _) (le_of_eq ?_); rw [pow_succ s]; unfold Q evenR; rw[pow_succ];ring
lemma wreath {x:X} (hs:0  ≤  s)(h: ContDiffAt ℝ ω f (s • x)) (k:ℕ): ‖iteratedFDeriv ℝ k (fun z=> f (s • z)) x‖  ≤  ‖iteratedFDeriv ℝ k f (s • x)‖*s^k:=by
   let L:=s • ContinuousLinearMap.id ℝ X; have hh:‖L‖ ≤ s:=by unfold L; rw [norm_smul,Real.norm_of_nonneg hs]; exact mul_le_of_le_one_right hs ContinuousLinearMap.norm_id_le
   rw[show (fun z=> f (s • z))= f ∘ L from rfl,iter_lin_at (show ContDiffAt ℝ k f (L x) from h.of_le le_top)]
   refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ?_; rw [prod_const,card_univ,Fintype.card_fin]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) (norm_nonneg _)
lemma heaven (d:ℕ)(R:ℝ)(hR:0 ≤ R)(hs:0  ≤  s)(hv:s ≤ 1)(h:∀ x:X,‖x‖ ≤ R*s→Allows k f x C)(hC:0 ≤ C)(hd:d ≤  k)(ht:∀ i:ℕ,i<d→‖iteratedFDeriv ℝ i f 0‖ ≤  C*s^(d-i))(x:X)(hx:‖x‖ ≤ R) : Allows k (fun z:X=> f (s • z)) x (C*evenR d R*s^d):=by
    have hh: ‖s • x‖ ≤  R*s:=by rw [norm_smul_of_nonneg hs,mul_comm]; exact mul_le_mul_of_nonneg_right hx hs
    have he:= (h (s • x) hh).analytic; refine ⟨he.comp (f:=fun z:X=>s • z) x (contDiffAt_const.smul contDiffAt_id),fun i hi=> ?_⟩; apply (wreath hs he i).trans; by_cases hk:i<d
    · have hm:i+(d-i)=d:=by omega
      have ht':= haloA (k:=i) (d-i) R hR hs (fun x hx=> (h x hx).order (by omega)) hC (fun j he hp=> by rw[hm]; exact ht _ (by omega)) (s • x) hh
      refine (mul_le_mul_of_nonneg_right ht' (pow_nonneg hs i)).trans ?_; rw [mul_assoc,← pow_add,show d-i+i=d by omega]; refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hC) (by positivity); exact pow_le_pow_right₀ (le_add_of_nonneg_right hR) (by omega)
    exact mul_le_mul (((h _ hh).norm_le i hi).trans (le_mul_of_one_le_right hC (one_le_pow₀ (le_add_of_nonneg_right hR)))) (pow_le_pow_of_le_one hs hv (by omega)) (by positivity) (mul_nonneg hC (pow_nonneg (by linarith only[hR]) _))
end YM.Trace.Turret
