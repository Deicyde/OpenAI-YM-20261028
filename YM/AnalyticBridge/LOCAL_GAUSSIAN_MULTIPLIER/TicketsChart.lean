import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Visit
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Broad



/-!
# Pre-L chart charges for held or fixed-Z uses

Normalize in the chosen **step width** (post-L). Every differentiated
profile then gets this direction currency as well; no charge per unstruck
cutoff. Actual estimates for every admitted `LocalRatio` and χ here
(including d→0 and the equality boundaries inside the chosen true chart).
Gives `Outlook` inputs using mean/velocity differences too. There is no
universal linear-distance price across an arbitrary geometry change. For
using two means, align the physical link first.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussian
open Function Filter Set Lattice RG Wilson ProjectorNext.Equivariance Next.SectorChange
  YM.Push.SectorMeasure YM.Next.Foundations Precision MeasureTheory Metric
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff Classical

lemma budgetThrough (k : ℕ) : (k:ℕ∞ω) ≤ ∞ := WithTop.coe_le_coe.mpr (show (k:ℕ∞) ≤ ⊤ from le_top)

lemma Farewell.shelf {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {p : Set E} {k : ℕ} (hs : IsCompact p) (hf : ∀ x∈p, ContDiffAt ℝ k f x) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ x∈p, Farewell f x k W := by
  have hh (j : Fin (k+1)) : ∃ W : ℝ, 1 ≤ W ∧ ∀ x∈p, ‖iteratedFDeriv ℝ (j:ℕ) f x‖ ≤ W := by
    let g x := ‖iteratedFDeriv ℝ (j:ℕ) f x‖
    have he : (j:ℕ) ≤ k := Nat.le_of_lt_succ j.isLt
    have hg : ContinuousOn g p := fun i hi => ((hf i hi).continuousAt_iteratedFDeriv (by exact_mod_cast he)).norm.continuousWithinAt
    obtain ⟨W,hW⟩ := (hs.image_of_continuousOn hg).bddAbove
    exact ⟨max 1 W,le_max_left ..,fun x hx => (hW (mem_image_of_mem g hx)).trans (le_max_right ..)⟩
  choose w hw hs using hh
  refine ⟨1+∑ i,w i, le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => zero_le_one.trans (hw _))),fun i hi n hn => ?_⟩
  exact (hs ⟨n,Nat.lt_succ_of_le hn⟩ i hi).trans ((Finset.single_le_sum (fun x _ => zero_le_one.trans (hw x))
    (Finset.mem_univ _)).trans (le_add_of_nonneg_left zero_le_one))



lemma Farewell.dead {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : E → ℝ}
    {k : ℕ} {r : ℝ} {x : E} (hr : 0 ≤ r) (h : v =ᶠ[𝓝 x] 0) : Farewell v x k r := by
  intro i hi; rw [(h.iteratedFDeriv (𝕜:=ℝ) i).eq_of_nhds,iteratedFDeriv_zero]; simpa

variable {G : Gauge} {d r : ℝ}

lemma broad_scale (q : Chi) (hd : 0<d) (s : ℝ) (y : G.Color) : broad q (d*s) (d • y) = broad q s y := by
  unfold broad Chi.innerShare; rw [norm_smul,Real.norm_of_nonneg hd.le,mul_div_mul_left _ _ hd.ne']
lemma broad_grade (q : Chi) (k : ℕ) (s : ℝ) (hs : 0<s) :
    ∃ W : ℝ, 1 ≤ W ∧ ∀ x : G.Color,Farewell (broad q s) x k W := by
  let p := closedBall (0:G.Color) (2*s)
  obtain ⟨w,h1,he⟩ := Farewell.shelf (isCompact_closedBall (0:G.Color) (2*s)) (fun p _ => ((broad_smooth q s).of_le (budgetThrough k)).contDiffAt)
  refine ⟨w,h1,fun p => ?_⟩
  by_cases hv : ‖p‖ ≤ 2*s
  · exact he p (by simpa)
  apply Farewell.dead (zero_le_one.trans h1)
  filter_upwards [continuous_norm.continuousAt (x:=p) |>.eventually (lt_mem_nhds (lt_of_not_ge hv))] with y hy
  exact Classical.not_not.mp (fun (hh : broad q s y≠0) => (broad_span q hs y hh).not_ge (show 2*s<‖y‖ from hy).le)

/-- A useful fixed-germ scaling cancellation. DOESN'T apply to a Haar
ratio from a different chart or to a retuned profile. -/
lemma Farewell.still {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {f : E → ℝ}
    {s : ℝ} (hf : ContDiff ℝ ∞ f) (hg : f 0=0) (hz : fderiv ℝ f 0=0) (hs : 0 ≤ s) (k : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ d ∈ Ioc (0:ℝ) 1, ∀ x : E, ‖x‖ ≤ s → Farewell (fun y => f (d • y)) x k (W*d^2) := by
  let t := closedBall (0:E) s; let g := fderiv ℝ f
  have hh : ContDiff ℝ ∞ g := hf.fderiv_right (by simp)
  obtain ⟨W,h1,h⟩ := Farewell.shelf (f:=f) (k:=k+2) (p:=t) (isCompact_closedBall _ _) (fun i _ => (hf.of_le (budgetThrough _)).contDiffAt)
  have hw := zero_lt_one.trans_le h1
  have ht : 0 ∈ t := mem_closedBall_self hs
  have hp (x : E) (hx : x ∈ t) : ‖g x‖ ≤ W*‖x‖ := by
    have he (a : E) (ha : a∈t) : ‖fderiv ℝ g a‖ ≤ W := by
      rw [← norm_iteratedFDeriv_one (𝕜:=ℝ) g,norm_iteratedFDeriv_fderiv]; exact h a ha _ (by omega)
    simpa only [g,hz,sub_zero] using! ((convex_closedBall (0:E) s).norm_image_sub_le_of_norm_fderiv_le (fun i _ => hh.differentiable (by simp) _) he ht hx)
  let M := W*(1+s+s^2)
  have hm : M > 0 := by unfold M; positivity
  have hw' : W ≤ M := le_mul_of_one_le_right hw.le (by nlinarith only [hs,sq_nonneg s])
  refine ⟨M,hm,fun d hd x hx i hi => ?_⟩
  have hd1 := hd.2; have hd0 := hd.1
  let y := d • x
  have hy : ‖y‖ ≤ d*s := by unfold y; rw [norm_smul,Real.norm_of_nonneg hd0.le]; gcongr
  have hx : y ∈ closedBall (0:E) (d*s) := by simpa
  have hds : d*s ≤ s := mul_le_of_le_one_left hs hd1
  have ht : closedBall (0:E) (d*s) ⊆ t := closedBall_subset_closedBall hds
  rw [iteratedFDeriv_comp_const_smul d (hf.of_le (budgetThrough i)), norm_smul,Real.norm_of_nonneg (pow_nonneg hd0.le _)]
  cases i with
  | zero =>
    simp only [pow_zero,one_mul,norm_iteratedFDeriv_zero]
    have he i (hi : i ∈ closedBall (0:E) (d*s)) : ‖fderiv ℝ f i‖ ≤ W*(d*s) :=
      (hp i (ht hi)).trans (mul_le_mul_of_nonneg_left (by simpa using hi) hw.le)
    have hz : ‖f y‖ ≤ W*(d*s)*‖y‖ := by
      simpa only [hg,sub_zero] using! (convex_closedBall (0:E) (d*s)).norm_image_sub_le_of_norm_fderiv_le
        (fun i _ => hf.differentiable (by simp) _) he (mem_closedBall_self (mul_nonneg hd0.le hs)) hx
    calc
      _ ≤ W*s^2*d^2 := hz.trans ((mul_le_mul_of_nonneg_left hy (mul_nonneg hw.le (mul_nonneg hd0.le hs))).trans_eq (by ring))
      _ ≤ _ := by unfold M; gcongr; linarith
  | succ i =>
    cases i with
    | zero =>
      rw [pow_one,norm_iteratedFDeriv_one]; unfold M
      calc
        _ ≤ W*s*d^2 := (mul_le_mul_of_nonneg_left ((hp y (ht hx)).trans (mul_le_mul_of_nonneg_left hy hw.le)) hd0.le).trans_eq (by ring)
        _ ≤ _ := by gcongr; nlinarith only [sq_nonneg s]
    | succ i =>
      have ha : i+1+1 ≤ k+2 := by omega
      rw [mul_comm M (d^2)]
      exact mul_le_mul (pow_le_pow_of_le_one hd0.le hd1 (by omega)) ((h y (ht hx) _ ha).trans hw') (norm_nonneg _) (sq_nonneg _)

-- Log gets its **full normalized** through-k price. Covers boundaries
-- of the committed proof with a genuine larger chart; cutoff included.

end YM.AnalyticBridge.LocalGaussian
