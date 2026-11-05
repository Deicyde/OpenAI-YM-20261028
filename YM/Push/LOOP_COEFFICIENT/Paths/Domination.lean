import YM.Push.LOOP_COEFFICIENT.Pullback
import YM.Work.B04
import YM.Work.F02.Series

/-!
# Degree-by-degree normal convergence on smaller balls; entire pieces
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Paths
open Function Filter Set Metric
open scoped Topology ContDiff BigOperators
variable {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F]
    {x : E} {f : E → F} {C r : ℝ}
lemma degree_bound (hr : 0<r) (k : ℕ) : ∃ s D : ℝ,0<s ∧ s≤r ∧ 0<D ∧ ∀ {E F : Type} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F] {f : E → F} {x : E} {C},
    ContDiff ℂ ω f → (∀ z ∈ ball x r, ‖f z‖≤ C) → ∀ z ∈ ball x s, ∀ j≤k, ‖iteratedFDeriv ℂ j f z‖ ≤ D*C := by
  induction k with
  | zero => refine ⟨r,1,hr,le_rfl,one_pos,fun h he z hz j hj => ?_⟩; obtain rfl : j=0 := Nat.eq_zero_of_le_zero hj; simpa using! he z hz
  | succ k ih =>
    obtain ⟨s,D,hs,hs',hD,H⟩ := ih
    refine ⟨s/2,max D (D/(s/2)),half_pos hs,by linarith, hD.trans_le (le_max_left ..),fun h he z hz j hj => ?_⟩
    have hC := (norm_nonneg _).trans (he _ (mem_ball_self hr)); rcases Nat.lt_or_eq_of_le hj with hj|rfl
    · exact (H h he z (ball_subset_ball (half_le_self hs.le) hz) j (Nat.le_of_lt_succ hj)).trans (by gcongr; simp)
    have hh := Work.F02.fderiv_bound (h.differentiable_iteratedFDeriv (m:=k) (by simp)) hs (fun y hy => H h he y hy k le_rfl) hz
    rw [iteratedFDeriv_succ_eq_comp_left,comp_apply, LinearIsometryEquiv.norm_map]
    exact hh.trans (by rw [mul_div_right_comm]; gcongr; simp)

variable {ι : Type*} [CompleteSpace F] {u : ι → ℝ} {g : ι → E → F}
lemma iteratedFDeriv_sumBall_aux {r} {k : ℕ} (hg : ∀ i, ContDiff ℂ ω (g i)) (hu : Summable u) (hb : ∀ y∈ball x r, ∀ n≤k, ∀ i, ‖iteratedFDeriv ℂ n (g i) y‖ ≤ u i) :
    ∀ y∈ball x r, iteratedFDeriv ℂ k (fun y => ∑' i,g i y) y = ∑' i,iteratedFDeriv ℂ k (g i) y := by
  letI := NormedSpace.restrictScalars ℝ ℂ E
  induction k with
  | zero => intro y hy; simp only [iteratedFDeriv_zero_eq_comp, comp_apply]; exact (continuousMultilinearCurryFin0 ℂ E F).symm.toContinuousLinearEquiv.map_tsum
  | succ k ih =>
    intro y hy
    have he : iteratedFDeriv ℂ k (fun y => ∑' i,g i y) =ᶠ[𝓝 y] fun y => ∑' i,iteratedFDeriv ℂ k (g i) y := eventually_of_mem (isOpen_ball.mem_nhds hy) (ih (fun y hy n hn => hb y hy n (by omega)))
    have ht := hasFDerivAt_tsum_of_isPreconnected hu isOpen_ball (convex_ball x r).isPreconnected
      (fun i y _ => ((hg i |>.differentiable_iteratedFDeriv (m:=k) (by simp)) y).hasFDerivAt)
      (fun i y hy => by simpa only [iteratedFDeriv_succ_eq_comp_left,LinearIsometryEquiv.norm_map,comp_apply] using hb y hy (k+1) le_rfl i)
      hy (Summable.of_norm_bounded hu (hb y hy k (by omega))) hy
    simp only [iteratedFDeriv_succ_eq_comp_left,comp_apply,he.fderiv_eq,ht.fderiv]; exact (continuousMultilinearCurryLeftEquiv ℂ
        (fun _ : Fin (k + 1) => E) F).symm.toContinuousLinearEquiv.map_tsum

lemma iteratedFDeriv_hasSum (hr : 0<r) (k : ℕ) (hg : ∀ i, ContDiff ℂ ω (g i)) (hu : Summable u) (h : ∀ i,∀ z∈ball x r, ‖g i z‖≤u i) :
    HasSum (fun i => iteratedFDeriv ℂ k (g i) x) (iteratedFDeriv ℂ k (fun y => ∑' i,g i y) x) := by
  obtain ⟨s,D,hs,_,_,H⟩ := degree_bound hr k
  have he y hy n hn i := H (hg i) (h i) y hy n hn
  rw [iteratedFDeriv_sumBall_aux hg (hu.mul_left D) he x (mem_ball_self hs)]; exact (Summable.of_norm_bounded (hu.mul_left D) (he _ (mem_ball_self hs) _ le_rfl)).hasSum
end YM.Push.Loops.Paths
