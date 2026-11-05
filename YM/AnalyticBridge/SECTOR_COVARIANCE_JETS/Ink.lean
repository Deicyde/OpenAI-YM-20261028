import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Calc
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion

set_option warningAsError false

/-!
# Reference-period Q mixed chart derivatives in physical gauge

Price through k with matrix on the *oriented* rooted predictor, its oriented
k held. Covers the endpoint inverse V case by using the actual formula for
flipped input links, not identifying different tangent conventions at nonzero
field. Use `impression` before applying these to selected curved rows on
other periods.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance.Press
open Function Filter Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch
open YM.Push.SectorMeasure YM.Push YM.Next YM.Next.Fluctuations YM.Next.SectorChange Motion Metric
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Q input at three actual log arrays on the period; u datum,
B pulled coarse left chart, a pulled fine increment. -/
abbrev Trio (G : Gauge) (f : Side) := Directions G f × (Directions G f × Directions G f)

def unturned (v : Trio G f) : Config G f := increment (increment (increment 1 v.1) v.2.1) v.2.2

def imageGroup (flips : Bond f → Bool) (v : Trio G f) : Config G f :=
  fun i => if flips i then (unturned v i)⁻¹ else unturned v i

def pasteQ (t : S.Choices) (flips : Bond f → Bool) (i : Bond c) (v : Trio G f) :=
  S.prediction (imageGroup flips v) t i

def rateQ (t : S.Choices) (flips : Bond f → Bool) (i : Bond c) (v : Trio G f) : G.Color :=
  G.curvature (pasteQ t flips i v * (pasteQ t flips i (v.1,v.2.1,0))⁻¹)

lemma group_zero (flips : Bond f → Bool) : imageGroup flips (0:Trio G f) = 1 := by
  unfold imageGroup unturned
  simp [increment_zero]
  rfl

private lemma continuous_log_image (flips : Bond f → Bool) (i : Bond f) :
    ContDiff ℝ ω (fun v : Trio G f => G.mat (imageGroup flips v i)) := by
  let a : Directions G f → G.Mat := fun t => G.mat (G.lieExp (t i))
  have he : ContDiff ℝ ω a := G.exp_jet.comp (contDiff_apply ℝ G.Color i)
  have hx : ContDiff ℝ ω (fun v : Trio G f => G.mat (unturned v i)) := by
    simp_rw [unturned, increment, Pi.one_apply, mul_one,G.mat_mul]
    change ContDiff ℝ ω (fun v : Trio G f => a v.2.2 * (a v.2.1 * a v.1))
    exact (he.comp (contDiff_snd.comp contDiff_snd)).mul ((he.comp (contDiff_fst.comp contDiff_snd)).mul (he.comp contDiff_fst))
  unfold imageGroup; split
  · simp_rw [G.mat_inv]; exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.comp hx
  exact hx

private lemma works (h : S.patch.Branches S.kernel G) (t : S.Choices) (flips : Bond f → Bool) (i : Bond c) :
    ContDiffAt ℝ ω (fun x : Trio G f => G.mat (pasteQ t flips i x)) 0 := by
  let L (x : Trio G f) := imageGroup flips x
  let B (x : Trio G f) := Flat.labels fun i => G.plog (G.mat (L x i))
  have hx : B 0 = 0 := by
    funext i; unfold B Flat.labels L
    simp [group_zero]
  have hb (i : Bond f) := (continuous_log_image (G:=G) flips i)
  have ht : ContDiffAt ℝ ω B 0 := by
    unfold B Flat.labels; apply contDiffAt_pi.mpr; intro i
    let e : Bond f := (i.1,axisEquiv.symm i.2)
    apply ContDiffAt.comp _ (g:=G.plog) (f:=fun x => G.mat (L x e)) _ (hb e).contDiffAt
    rw [show G.mat (L 0 e)=1 from (by unfold L; rw [group_zero, Pi.one_apply,G.mat_one])]; exact G.plog_diff
  have he : ContDiffAt ℝ ω (fun x : Trio G f => G.mat (S.prediction (represent (B x)) t i)) 0 :=
    ContDiffAt.comp 0 (g:=fun y => G.mat (S.prediction (represent y) t i)) (f:=B) (hx.symm ▸ prediction_cont S h i t) ht
  apply he.congr_of_eventuallyEq
  have hv (e : Bond f) : ∀ᶠ x : Trio G f in 𝓝 0,G.lieExp (G.plog (G.mat (L x e)))=L x e := by
    refine Filter.Tendsto.eventually ?_ G.plog_right
    have H : Tendsto (fun x : Trio G f => L x e) (𝓝 0) (𝓝 (L 0 e)) :=
      (G.continuous_mat.isClosedEmbedding G.mat_injective).isEmbedding.tendsto_nhds_iff.mpr (hb e).continuous.continuousAt.tendsto
    rw [show L 0=1 from group_zero _] at H; exact H
  filter_upwards [Filter.eventually_all.mpr hv] with v hv
  have hx : represent (B v)=L v := by
    unfold represent B; rw [Flat.collected]; funext i; dsimp only [increment]; rw [hv]; exact mul_one _
  rw [hx]; rfl

lemma ratePlot (h : S.patch.Branches S.kernel G) (t : S.Choices) (flips : Bond f → Bool) (i : Bond c) :
    ContDiffAt ℝ ω (rateQ (G:=G) t flips i) 0 := by
  let L (x : Trio G f) := (x.1,x.2.1,(0:Directions G f))
  have ht := works h t flips i
  apply curvature_diff_mat _ _
  simp_rw [G.mat_mul,G.mat_inv]
  apply ht.mul ((show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp _ ?_)
  apply ht.comp (f:=L) (x:= (0:Trio G f))
  exact contDiffAt_fst.prodMk ((contDiffAt_fst.comp _ contDiffAt_snd).prodMk contDiffAt_const)

/-- Uniform on each fixed reference torus. Jet price even at B,u nonzero. -/
lemma plotted (S : StepData c f) (h : S.patch.Branches S.kernel G) (k : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ (t : S.Choices) (flips : Bond f → Bool) (i : Bond c) (x : Trio G f),
      ‖x‖ ≤ r → ContDiffAt ℝ ω (fun v : Trio G f => G.mat (pasteQ t flips i v)) x ∧
        ContDiffAt ℝ ω (rateQ t flips i) x ∧ AtCap k C (rateQ t flips i) x := by
  let Y := S.Choices × ((Bond f → Bool) × Bond c)
  let F (v : Y) := rateQ (G:=G) v.1 v.2.1 v.2.2
  let M (v : Y) := fun x : Trio G f => G.mat (pasteQ v.1 v.2.1 v.2.2 x)
  have hf v : ContDiffAt ℝ ω (F v) 0 := ratePlot h ..
  have hm v : ContDiffAt ℝ ω (M v) 0 := works h ..
  let J := Y × Fin (k+1)
  let D (j : J) (x : Trio G f) := iteratedFDeriv ℝ j.2.val (F j.1) x
  have he (j : J) : ∀ᶠ x : Trio G f in 𝓝 0, ‖D j x‖ ≤ ‖D j 0‖+1 := by
    have hh : ContinuousAt (fun x => ‖D j x‖) 0 := (ContDiffAt.continuousAt_iteratedFDeriv (hf j.1) le_top).norm
    filter_upwards [hh.tendsto.eventually (gt_mem_nhds (lt_add_one _))] with x hx; exact hx.le
  let C := 1+∑ j, ‖D j 0‖
  have hh : ∀ᶠ x : Trio G f in 𝓝 0, ∀ v : Y, ContDiffAt ℝ ω (M v) x ∧ ContDiffAt ℝ ω (F v) x ∧ AtCap k C (F v) x := by
    filter_upwards [Filter.eventually_all.mpr he,
      Filter.eventually_all.mpr (fun v => (hf v).eventually (by simp)),
      Filter.eventually_all.mpr (fun v => (hm v).eventually (by simp))] with x hx hl hp
    intro v
    refine ⟨hp v,hl v,(hl v).of_le le_top,fun i hi => ?_⟩
    let j : J := (v,⟨i,Nat.lt_succ_of_le hi⟩)
    have hv := single_le_sum (fun i _ => norm_nonneg (D i 0)) (mem_univ j)
    apply (hx j).trans; rw [add_comm]; exact add_le_add_right hv _
  obtain ⟨r,hr,hC⟩ := nhds_basis_closedBall.mem_iff.mp hh
  have ht : 0 ≤ ∑ j, ‖D j 0‖ := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨C,r,by unfold C; linarith,hr,fun t j i x hx => ?_⟩
  exact hC (Metric.mem_closedBall.mpr (by rw [dist_zero_right]; exact hx)) (t,j,i)
end YM.AnalyticBridge.Covariance.Press
