import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Roof.Moment


/-!
# Pay polynomial volume warrants from uniform-stationary invoices

In this operation Auxiliary ONLY, can spend poly(volume). These are not
 pre-L or perpetual contraction amounts on history torus. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lapis
open Filter Function Metric Lattice Wilson RG RG.Supply Input Precision Org Tree Exterior
open Gauge Matrix Finset Set Push Push.Uniform Bid
open ConnectedActivityE6 Blaze Brush 
 
open scoped Topology ContDiff BigOperators Classical
variable {ι κ : Type} [Fintype ι] [Fintype κ] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Gauge} {k j : ℕ} {n c f : Side}
variable {u : Positions ι → ℝ} {v : Positions ι→ Positions κ} {a M C r D B : ℝ} {x : Positions ι}
section algebra

def tollS (V:ℝ) (k:ℕ) (C:ℝ):=V^k*C
lemma raises (h : 1≤D) (hm : (Fintype.card ι:ℝ) ≤ D) (ht : 0≤C) (hy : k≤j)
    (hu : ∀ q:Fin k→ι, ‖entry u x q‖≤C) : normJ k u x ≤ tollS D j C := by
  have hh:0<D:=zero_lt_one.trans_le h
  apply ContinuousMultilinearMap.opNorm_le_bound (M:=tollS D j C) (by unfold tollS; positivity)
  intro z; unfold tollS; rw [Uniform.multi_expansion]
  refine (norm_sum_le ..).trans ?_
  let p := ∏ i, ‖z i‖; have hp : 0≤ p:= Finset.prod_nonneg fun _ _=> norm_nonneg _
  calc _ ≤ ∑ _q:Fin k→ι, C*p := sum_le_sum fun i _=> by rw [norm_mul,norm_prod,mul_comm C]; apply mul_le_mul _ (hu i) (norm_nonneg _) hp; exact prod_le_prod (fun _ _=>norm_nonneg _) (fun j _=> norm_le_pi_norm _ _)
       _ ≤ _ := by
         rw [sum_const,nsmul_eq_mul,card_univ,Fintype.card_fun,Nat.cast_pow,Fintype.card_fin]; rw [← mul_assoc]; apply mul_le_mul_of_nonneg_right _ hp
         exact mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ (Nat.cast_nonneg _) hm _).trans (pow_le_pow_right₀ h hy)) ht
lemma ratifyS (h : 1 ≤ D) (hm : (Fintype.card ι:ℝ) ≤ D) {l : ι→Site n} (hr : 0<a) (ht : 0≤C)
    (hg : Scatter l a j u x C) (hy : k≤j) (hk : 0 < k) : normJ k u x ≤ tollS D j C := by
  apply raises h hm ht hy; intro q; have he := hg k hy q ⟨0,hk⟩
  exact he.trans (mul_le_of_le_one_right ht (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (Nat.cast_nonneg _))))
lemma byline (h : 1≤D) (hm : (Fintype.card ι:ℝ) ≤ D) (ht : 0 ≤ C) (hx : ContDiffAt ℝ ω v x)
    (hv : ‖v x‖ ≤ r) {l : ι→Site n} {u : κ→ Site n} (hr : 0<a) (hg : Uniform.Envelope l u a j v x C) : Brush j (r+tollS D j C) 1 v x := by
  have hd := h; have hy := (norm_nonneg _).trans hv
  have hc:0 ≤ tollS D j C:= by unfold tollS; positivity
  refine Brush.fold (T:=fun i t=> v t i) zero_le_one (add_nonneg hy hc) fun i=> Brush.offer.2 ⟨((contDiffAt_pi.mp hx) i).of_le le_top,?_⟩
  intro k hk; rcases k with _|k
  · unfold normJ; rw [norm_iteratedFDeriv_zero]; exact ((norm_le_pi_norm _ i).trans hv).trans (le_add_of_nonneg_right hc)
  apply le_trans (raises h hm ht hk ?_) (le_add_of_nonneg_left hy)
  intro q; rw [entry_projects v hx]; exact (hg _ (Nat.succ_ne_zero k) hk q i).trans
    (mul_le_of_le_one_right ht (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) (Nat.cast_nonneg _))))

lemma horizonB (h:1≤D) (hm : (Fintype.card ι:ℝ) ≤ D) {l : ι→Site n} (ha : 0≤C) (hr : 0<a) (hg : 0<r)
    (hj : 1≤ j) (hx : x∈ball (0:Positions ι) r)
    (hd : ∀ i : Positions ι, i∈ball 0 r → Scatter l a j u i C ∧ ContDiffAt ℝ ω u i) :
    ‖u x - u 0‖≤tollS D j C * ‖x‖ ∧ Brush j (tollS D j C*(1+r)) 1 (u-fun _=>u 0) x := by
  have hp := (convex_ball (0:Positions ι) r).norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ) (f:=u) (fun i hi => (hd _ hi).2.differentiableAt (by simp)) (C:=tollS D j C)
    (fun y hy=> by rw [← norm_iteratedFDeriv_one]; exact ratifyS h hm hr ha (hd y hy).1 hj (by decide))
    (mem_ball_self hg) hx
  rw [sub_zero] at hp
  have he := (hd x hx).2; have hc : 0 ≤ tollS D j C := by unfold tollS; positivity
  refine ⟨hp, Brush.offer.2 ⟨(he.of_le le_top).sub contDiffAt_const,?_⟩⟩
  intro i hi; cases i with
  | zero => unfold normJ; rw [norm_iteratedFDeriv_zero]; exact hp.trans (mul_le_mul_of_nonneg_left ((mem_ball_zero_iff.mp hx).le.trans (le_add_of_nonneg_left zero_le_one)) hc)
  | succ i => unfold normJ; rw [iteratedFDeriv_sub_apply (he.of_le le_top) contDiffAt_const,iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]; exact (ratifyS h hm hr ha (hd x hx).1 hi (by omega)).trans (le_mul_of_one_le_right hc (le_add_of_nonneg_right hg.le))
lemma horizon0 (h:1≤D) (hm : (Fintype.card ι:ℝ) ≤ D) {l : ι→Site n} (ha : 0≤C) (hr : 0<a) (hg : 0<r) (hf : u 0=0)
    (hj : 1≤ j) (hx : x∈ball (0:Positions ι) r)
    (hd : ∀ i : Positions ι, i∈ball 0 r → Scatter l a j u i C ∧ ContDiffAt ℝ ω u i) : Brush j (tollS D j C*(1+r)) 1 u x := by
  have hz := (horizonB h hm ha hr hg hj hx hd).2; rwa [hf,show (fun _ : Positions ι=> (0:ℝ))=0 from rfl,sub_zero] at hz
end algebra
end YM.PhysicalNext.Repeat.Lapis
