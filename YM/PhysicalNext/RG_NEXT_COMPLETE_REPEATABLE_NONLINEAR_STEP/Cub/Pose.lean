import YM.AnalyticNext.GRID_STOP_ATTENUATION.Harvest.Eco
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Path
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Mallow.Pediment
import YM.Planned.PRIMARY_INTEGRAL_295.Gala
import YM.Planned.PRIMARY_INTEGRAL_295.Pillar

/-! # paid Canvas WITH FIXED identity gauge 

 At identity only. Spells out one direction price step of Canvas so we can specify which gauge; imports all Cube budgets; links must pay Wire.Ticket identical. No replacing later gauge L. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open JointLoad JointLoad.Heir
open Function Filter Set Metric Lattice Wilson Pressure RG Tree Next Next.Fluctuations Next.SectorChange
   Exterior Bloch Bid AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular.Foliage
open WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : BudgetPoint} {V : Config G c} {g : Site c → G.El} {Y : Support c} {o : Site c} {r l n : ℕ}

set_option maxHeartbeats 450000 in
lemma posed (Z : Collar G n)  (_hk : Cube.Wire P r Z)
    : Canvas P o r (1:Config G c) 1 n (Cube.fee Z) := by
  classical
  let V:Config G c:=1; let g:Site c→ G.El:=1
  change Canvas P o r V g n _
  have seen (i:Bond c)(_:separation o i.1≤r) : G.mat (gauge g V i) ∈ ball 1 Z.r:=by simp [g,V,Lattice.gauge,Z.pos]
  have hh : ∀ᶠ W in 𝓝 V, ∀ i:Bond c,separation o i.1 ≤ r → G.mat (gauge g W i) ∈ ball 1 Z.r := by
    apply eventually_all.mpr; intro i; by_cases hi : separation o i.1 ≤ r
    · simp only [hi,true_implies]
      exact (show Continuous (fun W : Config G c => G.mat (gauge g W i)) by unfold Lattice.gauge; fun_prop).continuousAt.eventually (isOpen_ball.mem_nhds (seen i hi))
    exact Eventually.of_forall fun _ ht => (hi ht).elim
  have h0 := Cube.fee_one Z; have hp := P.threshold_pos
  have h₁ := (Cube.stamps G Z).choose_spec

  refine ⟨hh.mono (fun W h i hi => ?_),contDiffAt_pi.mpr (fun i => ?_),fun i hi => ?_,fun A => contDiffAt_pi.mpr (fun i => ?_),fun {l} A q hl hA j hj hJ i => ?_⟩
  · change separation o i.1 ≤ r at hi; rw [increment,Heir.crop, if_pos hi]; exact (mul_one (G.lieExp _)).trans (Z.group _ (ball_subset_closedBall (h i hi))) |>.symm
  · simp only [Function.comp_apply,Heir.crop]; split; swap; exact contDiffAt_const
    next hi =>
    let w (z : Directions G c) := G.mat (gauge g (increment V z) i)
    have hq : ContDiff ℝ ω w := by
      simp only [w,Lattice.gauge,increment,G.mat_mul]; exact (contDiff_const.mul ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const)).mul contDiff_const
    apply ContDiffAt.comp (f:=w) (g:=G.plog) 0 _ hq.contDiffAt
    unfold w; rw [Work.G07.at_zero_increment]; exact (Z.log _ (ball_subset_closedBall (seen i hi))).analytic
  · rw [Heir.crop,if_pos hi]; simp only [g,V,Lattice.gauge,Pi.one_apply,inv_one,mul_one,G.mat_one,G.plog_one,norm_zero]; positivity
  · simp only [launch,Function.comp_apply,Heir.crop]; split; swap; exact contDiffAt_const
    next hi =>
    let w z := G.mat (gauge g (journey V _ A z) i)
    let φ (z : Panels _) := fun j => z j • A j i
    have hw : ContDiff ℝ (n:ℕ∞ω) w := by
      unfold w Lattice.gauge journey; simp_rw [Cube.starts_expanded,G.mat_mul]
      exact ((contDiff_const.mul ((((Cube.starts_diff G _).comp (f:=φ) (by unfold φ; fun_prop)).of_le le_top).mul contDiff_const)).mul contDiff_const)
    apply ContDiffAt.comp (g:=G.plog) (f:=w) 0 _ hw.contDiffAt
    unfold w; rw [Planned.AtomRegular.Sample.journey_origin]; exact ((Z.log _ (ball_subset_closedBall (seen i hi))).analytic).of_le le_top
  simp only [launch,Function.comp_apply,Heir.crop]; split; swap; simp
  next hi =>
  let L : Panels l →L[ℝ] Cube.carriage G l := ContinuousLinearMap.pi (fun j => (ContinuousLinearMap.proj j).smulRight (A j i))
  let f (z : Cube.carriage G l) := G.plog (G.mat (g i.1 * (Cube.starts G _ z * V i) * (g (i.1+step i.2))⁻¹))
  let w := P.threshold*spine P.power i.1 q; have hw := mul_pos hp (spine_pos P.power i.1 q)
  have h : Allows n f 0 (Cube.cap Z) := h₁.2 l hl _ _ _ (ball_subset_closedBall (seen i hi))
  have hL : ‖L‖ ≤ w := by
    refine ContinuousLinearMap.opNorm_le_bound _ hw.le (fun v => (pi_norm_le_iff_of_nonneg (show 0 ≤ w * ‖v‖ by positivity)).mpr fun t => ?_)
    rw [show L v t=v t • A t i from rfl, norm_smul, mul_comm w]; exact mul_le_mul (norm_le_pi_norm ..) (hA t i) (norm_nonneg _) (norm_nonneg v)
  rw [show (fun z => G.plog (G.mat (gauge g (journey V l A z) i))) = f ∘ L from funext fun z => by rw [Lattice.gauge,journey,Cube.starts_expanded]; rfl]
  rw [Push.Uniform.iter_lin_at (show ContDiffAt ℝ (j:ℕ∞ω) f (L 0) by rw [map_zero]; exact h.analytic.of_le le_top),L.map_zero]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact mul_le_mul ((h.norm_le j hJ).trans (le_add_of_nonneg_right (mul_nonneg Z.count_pos.le (by have := G.colorScale_pos; positivity)))) (pow_le_pow_left₀ (norm_nonneg _) hL _) (pow_nonneg (norm_nonneg _) _) (zero_le_one.trans h0)

lemma blankBirth (r:ℕ)(o:Site c) : Heir.crop o r (1:Site c→G.El) (1:Config G c)=0:=by
  ext1 i; unfold Heir.crop; split; · simp [Lattice.gauge]
  exact rfl
end YM.PhysicalNext.Repeat.Cub
