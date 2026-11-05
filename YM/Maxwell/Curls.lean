import YM.Maxwell.PotentialKernel

/-!
# The ordinary two-curl kernel obeys both leg equations

`bareCurl a b k m (x-y)` is F_ab as first insertion at x, F_km as second
at y, scalar for one color (different colors have zero covariance). Include
the sign from y-differentiation. Used before any test or analytic continuation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Maxwell
open Set Function Filter Analysis
open scoped Topology ContDiff BigOperators

/-- Apply a curl on the opposite endpoint to uncolored potential leg b. -/
def curlOpp (b k m : Axis) : E4 → ℝ :=
  (if k=b then grad m Green else 0) - (if m=b then grad k Green else 0)

def bareCurl (a b k m : Axis) := grad a (curlOpp b k m) - grad b (curlOpp a k m)

namespace Bare
variable {x : E4} {k m : Axis}

lemma choose_diff (hx : x ≠ 0) (k m a : Axis) :
    ContDiffAt ℝ ∞ (if a = k then grad m Green else 0) x := by
  split_ifs
  · exact gradGradientSmooth hx _
  exact contDiffAt_const

lemma opp_diff (hx : x ≠ 0) (b k m : Axis) : ContDiffAt ℝ ∞ (curlOpp b k m) x :=
  (choose_diff hx b m k).sub (choose_diff hx b k m)

lemma grad_sub {x} {f g : E4 → ℝ} (hf : ContDiffAt ℝ ∞ f x) (hg : ContDiffAt ℝ ∞ g x) (k) :
    grad k (f-g) x = grad k f x - grad k g x := by
  unfold grad D
  rw [fderiv_sub (hf.differentiableAt (by simp)) (hg.differentiableAt (by simp))]
  rfl

lemma chooseD (k m a b : Axis) (x) : grad b (if a=k then grad m Green else 0) x = if a=k then grad b (grad m Green) x else 0 := by
  split_ifs with H
  · rfl
  simp [grad,D]

lemma opp_grad (hx : x ≠ 0) (a b k m) : grad a (curlOpp b k m) x =
    (if k=b then grad a (grad m Green) x else 0) - if m=b then grad a (grad k Green) x else 0 := by
  rw [curlOpp, grad_sub (choose_diff hx b m k) (choose_diff hx b k m), chooseD, chooseD]

lemma opp_divergence (hx : x ≠ 0) (k m) : ∑ b : Axis, grad b (curlOpp b k m) x = 0 := by
  simp [opp_grad hx, Finset.sum_sub_distrib,Hess_sym hx k m]

lemma opp_harmonic (hx : x ≠ 0) (b k m) : ∑ i : Axis, grad i (grad i (curlOpp b k m)) x = 0 := by
  have he (a : Axis) : grad a (curlOpp b k m) =ᶠ[𝓝 x]
      ((if k=b then grad a (grad m Green) else 0) - (if m=b then grad a (grad k Green) else 0)) := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy
    rw [opp_grad hy]; split_ifs <;> rfl
  have ht (a i l : Axis) : ContDiffAt ℝ ∞ (if i=b then grad a (grad l Green) else 0) x := by
    split_ifs
    · exact HessSmooth hx _ _
    exact contDiffAt_const
  have h (a) : grad a (grad a (curlOpp b k m)) x =
      grad a (if k=b then grad a (grad m Green) else 0) x - grad a (if m=b then grad a (grad k Green) else 0) x :=
    (GermD _ (he a)).trans (grad_sub (ht a k m) (ht a m k) a)
  simp_rw [h, Finset.sum_sub_distrib]
  have hz : ∑ a : Axis, grad a (0 : E4 → ℝ) x = 0 := by simp [grad,D]
  split_ifs <;> simp [harmonic_gradient hx, hz]

lemma noGrad (hx : x ≠ 0) (b k m) : ∑ i : Axis, grad i (grad b (curlOpp i k m)) x = 0 := by
  have hw (i) : grad i (grad b (curlOpp i k m)) x = grad b (grad i (curlOpp i k m)) x :=
    grad_comm ((opp_diff hx _ _ _).of_le (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)) ..
  simp_rw [hw, ← grad_sum (fun i => grad i (curlOpp i k m))
    (fun i => grad_smooth _ (opp_diff hx _ _ _) (by simp))]
  have he : (fun y => ∑ b : Axis, grad b (curlOpp b k m) y) =ᶠ[𝓝 x] fun _ => (0:ℝ) := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy
    exact opp_divergence hy ..
  exact (GermD (basis b) he).trans (by simp [D])

theorem curl_diff (hx : x ≠ 0) (a b k m) : ContDiffAt ℝ ∞ (bareCurl a b k m) x :=
  (grad_smooth _ (opp_diff hx _ _ _) (m := ∞) (by simp)).sub
    (grad_smooth _ (opp_diff hx _ _ _) (m := ∞) (by simp))

theorem equation (k m : Axis) : WaveOn away (fun a b => bareCurl a b k m) := by
  refine ⟨fun a b _ hx => curl_diff hx _ _ _ _, ?_, ?_, ?_⟩
  · intro a b x hx; simp [bareCurl]
  · intro a b c x hx
    have hd (a i) : ContDiffAt ℝ ∞ (grad a (curlOpp i k m)) x := grad_smooth _ (opp_diff hx _ _ _) (by simp)
    unfold bareCurl
    rw [grad_sub (hd b c) (hd c b), grad_sub (hd c a) (hd a c), grad_sub (hd a b) (hd b a)]
    have hw (i) : ContDiffAt ℝ 2 (curlOpp i k m) x := (opp_diff hx _ _ _).of_le
      (show ((↑(2 : ℕ)) : WithTop ℕ∞) ≤ ∞ from WithTop.coe_le_coe.mpr le_top)
    nth_rw 1 [grad_comm (hw c) a b]
    nth_rw 1 [grad_comm (hw b) a c]
    nth_rw 1 [grad_comm (hw a) b c]
    abel
  intro b x hx
  have hd (a i) : ContDiffAt ℝ ∞ (grad a (curlOpp i k m)) x := grad_smooth _ (opp_diff hx _ _ _) (by simp)
  have hev (i) := grad_sub (hd i b) (hd b i) i
  simp_rw [bareCurl, hev, Finset.sum_sub_distrib, opp_harmonic hx, noGrad hx, sub_zero]

theorem even (hx : x ≠ 0) (a b k m) : bareCurl a b k m (-x) = bareCurl a b k m x := by
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  simp [bareCurl,opp_grad hnx,opp_grad hx,second_Green hx, second_Green hnx]

theorem exchange (hx : x ≠ 0) (a b k m) : bareCurl a b k m x = bareCurl k m a b x := by
  simp only [bareCurl, Pi.sub_apply,opp_grad hx]
  nth_rw 1 [Hess_sym hx a m]; nth_rw 1 [Hess_sym hx a k]
  nth_rw 1 [Hess_sym hx b m]; nth_rw 1 [Hess_sym hx b k]
  simp only [eq_comm]
  abel

theorem equation_right (a b : Axis) : WaveOn away (bareCurl a b) := by
  have hw (k m : Axis) {x} (hx : x ≠ 0) : bareCurl a b k m =ᶠ[𝓝 x] bareCurl k m a b := by
    filter_upwards [open_away.mem_nhds (show x ∈ away from hx)] with y hy; exact exchange hy ..
  refine ⟨fun _ _ _ hx => curl_diff hx _ _ _ _, ?_, ?_, ?_⟩
  · intro k m x hx; nth_rw 1 [exchange hx a b k m]; nth_rw 1 [exchange hx a b m k]
    exact (equation a b).form k m x hx
  · intro u v w x hx
    have he (i k l) : grad i (bareCurl a b k l) x = grad i (bareCurl k l a b) x := GermD _ (hw k l hx)
    rw [he u, he v, he w]
    exact (equation a b).cycle u v w x hx
  · intro u x hx
    have he (i) : grad i (bareCurl a b i u) x = grad i (bareCurl i u a b) x := GermD _ (hw i u hx)
    simp_rw [he]; exact (equation a b).divergence u x hx

end Bare
end YM.Maxwell
