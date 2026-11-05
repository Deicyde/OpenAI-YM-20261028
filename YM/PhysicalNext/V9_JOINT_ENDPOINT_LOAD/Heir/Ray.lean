import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Banjo
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Awards
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Ghost

/-! Weight-four Taylor when only TWO grades plus remainder are tapered.
Needs only Deep2 on the deterministic leading map, and no mask-inspecting
regular derivative or `k+1` argument on the highest-order channel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Lattice Wilson RG Next.Foundations
    AnalyticBridge.VerifiedReset MultiNext.SignedSource MultiNext.SignedSource.Mom MultiNext.SignedSource.Banjo
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {n : Side} {B : BudgetPoint} {X : Support n} {o : Site n} {m k : ℕ} {C r τ : ℝ}
    {f : Config G n → ℝ}

variable (g : G.Simple) (h : Seed B o X f) (hX : Nonwrapping X o) (hn : 4 ≤ n.val)
    (hb : B.supBounds o X f τ) (hr : 0 ≤ r) (ht : r ≤ 1) (hc : 1 ≤ C) (Q : Rights G k) (hk : k ≤ B.order)

include g h hn hX in
private lemma extinguish (a : Fin m → ℕ) (v : Fin m → Directions G n)
    (he : ∑ i,a i ≤ 4) (hA : ∀ i, 1 ≤ a i) (hv : ∀ i, a i ≤ 2 → screen X (v i) ∈ Mom.Maps o X (a i)) :
    iteratedFDeriv ℝ m (f ∘ increment 1) 0 v = 0 := by
  by_cases hx : ∃ i, 2 < a i
  · obtain ⟨i,hi⟩ := hx
    have hm : (Finset.univ.erase i).card+1=m := (Finset.card_erase_add_one (Finset.mem_univ i)).trans (by simp)
    have hs := Finset.sum_le_sum (s:= Finset.univ.erase i) (f:=fun _ => 1) (fun i _ => hA i); rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at he
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at hs
    change (Finset.univ.erase i).card ≤ ∑ j ∈ Finset.univ.erase i, a j at hs
    have hM : 0 < m := i.pos
    rcases show m=1 ∨ m=2 by omega with hj|hj
    · subst m; rw [iteratedFDeriv_one_apply, show fderiv ℝ (f ∘ increment 1) 0=0 from flat_critical g h.good]; rfl
    subst m
    change iteratedFDeriv ℝ 2 (f ∘ increment 1) 0 _ = _
    rw [show v= ![v 0,v 1] from funext fun i => by fin_cases i <;> rfl]
    change logHessian f (v 0) (v 1)=0
    have hz : a 0 + a 1 ≤ 4 := by rwa [Finset.add_sum_erase _ _ (Finset.mem_univ i),Fin.sum_univ_two] at he
    fin_cases i
    · have ht : a 1 = 1 := by change 2 < a 0 at hi; have := hA 1; omega
      rw [hessian_symm h.good]; exact h.constant_hessian g hX hn (by simpa only [ht] using hv 1 (show a 1 ≤ 2 by omega))
    · have ht : a 0 = 1 := by change 2 < a 1 at hi; have := hA 0; omega
      exact h.constant_hessian g hX hn (by simpa only [ht] using hv 0 (show a 0 ≤ 2 by omega))
  exact h.ghost g hX hn v hA he (fun i => hv i (le_of_not_gt (fun h => hx ⟨i,h⟩)))

include g h hn hX hb hr ht hc hk in
private lemma taper_zero (hm : m ≤ k) (v : Fin m → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) :
    ‖iteratedFDeriv ℝ m (f ∘ increment 1) 0 v‖ ≤ ((3*C)^k*r^5) * Q.fee * τ := by
  choose w hw hW hP using hv
  let T := iteratedFDeriv ℝ m (f ∘ increment 1) 0; change ‖T v‖ ≤ _
  have h0 := Q.large; have hτ := hb.1
  rw [funext hw,T.map_sum (α:=fun _ => Fin 3)]
  apply (norm_sum_le ..).trans
  refine (Finset.sum_le_sum (g:=fun _ => (C^m*r^5)*Q.fee*τ) (fun j _ => ?_)).trans ?_
  · let a (i : Fin m) := (j i).val+1
    by_cases he : ∑ i,a i ≤ 4
    · rw [show T _ = 0 from extinguish g h hX hn a _ he (fun _ => by unfold a; omega) (fun i hi => hP i _ (show (j i).val < 2 from Nat.lt_of_succ_le hi)),norm_zero]
      positivity
    apply (Q.born 1 _ (fun i => C*r^(a i)) hm (hm.trans hk) h.good hb (flat_ok B X) (fun i => hW i _)).trans
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]; simp only [Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht (by omega)) (by positivity)) (by positivity)) hτ
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,nsmul_eq_mul,Nat.cast_pow]
  have hi := pow_le_pow_right₀ (show 1 ≤ 3*C by linarith) hm
  calc
    _ = ((3*C)^m*r^5)*Q.fee*τ := by push_cast; rw [mul_pow]; ring
    _ ≤ _ := by gcongr

lemma along_deriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : E) (v : Fin m → E) (s : ℝ) {f : E → F} (hs : ContDiffAt ℝ (↑(m+1:ℕ)) f (s • u)) : HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ m f (t • u) v)
      (iteratedFDeriv ℝ (m+1) f (s • u) (Fin.cons u v)) s := by
  rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  exact (ContinuousMultilinearMap.apply ℝ _ F v).hasFDerivAt.comp_hasDerivAt s ((hs.differentiableAt_iteratedFDeriv
    (m:=m) (Nat.cast_lt.mpr (Nat.lt_succ_self _))).hasFDerivAt.comp_hasDerivAt s (show HasDerivAt (fun t : ℝ => t • u) u s from by simpa using (hasDerivAt_id' s).smul_const u))

include g h hn hX hb hr ht hc hk in
/-- Leading rescaled E deterministic pay at matching `u,v`.
Caller has to fit these actual chart conditions, see also `coaches`.
No PiVanish assumptions. -/
lemma ray (u : Directions G n) (hu : Promise 2 C r B o X u) (he : ∀ e, needed X e → ‖u e‖ ≤ 1 ∧ Lyre.width B o e ≤ 1)
    (hs : ∀ t ∈ Set.Icc (0:ℝ) 1, Healthy B.threshold X (increment 1 (t • u))) (hK : 5 ≤ k) (hm : m ≤ k) (v : Fin m → Directions G n)
    (hv : ∀ j, Promise 2 C r B o X (v j)) : ‖iteratedFDeriv ℝ m (f ∘ increment 1) u v‖ ≤ (k+1:ℝ)*((3*C)^k*r^5) * Q.fee * τ := by
  let F := f ∘ increment (1:Config G n); let z := ((3*C)^k*r^5)*Q.fee*τ
  have h0 := Q.large; have hτ := hb.1
  have H (j) (hj : j ≤ k) (v : Fin j → Directions G n) (hv : ∀ i, Promise 2 C r B o X (v i)) (s : ℝ) (ht' : s ∈ Set.Icc (0:ℝ) 1) :
      ‖iteratedFDeriv ℝ j F (s • u) v‖ ≤ ((k+1-j:ℕ):ℝ)*z := by
    have Hs t i (h : t ∈ Set.Icc (0:ℝ) 1) (hi : i ≤ k) : ContDiffAt ℝ (i:ℕ∞ω) F (t • u) := (along ‹Seed ..›.good (hs t h)).of_le (Nat.cast_le.mpr (hi.trans hk))
    induction hj using Nat.decreasingInduction generalizing s with
    | self =>
      rw [show k+1-k=1 by omega,Nat.cast_one,one_mul]
      apply (Q.moves 1 _ v (fun _ => 3*C*r) le_rfl hk ‹Seed ..›.good hb (hs _ ht') ?_ ?_).trans
      · simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow]; unfold z; rw [mul_pow]; exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr ht hK) (by positivity)) (by positivity)) hτ
      · intro i hi; rw [Pi.smul_apply,norm_smul, Real.norm_of_nonneg ht'.1]; exact ⟨mul_le_one₀ ht'.2 (norm_nonneg _) (he i hi).1,(he i hi).2⟩
      intro i; convert (hv i).shot hr ht (zero_le_one.trans hc) using 1; norm_num
    | of_succ j hj ih =>
      have ha : ∀ i : Fin (j+1), Promise 2 C r B o X ((Fin.cons u v : Fin (j+1) → Directions G n) i) := Fin.cases (by simpa using hu) (fun i => by simpa using hv i)
      have H := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f:=fun t : ℝ => iteratedFDeriv ℝ j F (t • u) v) (fun x hx => (along_deriv u v x (Hs x (j+1) hx hj)).hasDerivWithinAt)
        (fun x hx => ih (Fin.cons u v) ha x hx) (convex_Icc ..) (show (0:ℝ)∈Set.Icc (0:ℝ) 1 by simp) ht'
      rw [zero_smul,sub_zero, Real.norm_of_nonneg ht'.1] at H
      have hp := H.trans (mul_le_of_le_one_right (by unfold z; positivity) ht'.2)
      have he : ‖iteratedFDeriv ℝ j F 0 v‖ ≤ z := taper_zero g ‹Seed ..› hX hn hb hr ht hc Q hk (Nat.le_of_lt hj) v hv
      refine (norm_le_of_pair hp he).trans_eq ?_
      rw [show k+1-j=k+1-(j+1)+1 by omega, Nat.cast_add_one, add_mul,one_mul]
  have hx := H m hm v hv 1 (by simp); rw [one_smul] at hx
  refine hx.trans ((mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le ..)) (by unfold z; positivity)).trans_eq ?_); unfold z; push_cast; ring
where norm_le_of_pair {x y a b : ℝ} (h : ‖x-y‖ ≤ a) (he : ‖y‖ ≤ b) : ‖x‖ ≤ a+b :=
  (by simpa using (norm_add_le (x-y) y).trans (add_le_add h he))
end YM.PhysicalNext.JointLoad.Heir
