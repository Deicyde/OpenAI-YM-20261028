import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Quaver
import YM.Planned.ATOM_REGULAR_ESTIMATE.OpenPanel
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
import YM.Planned.ATOM_REGULAR_ESTIMATE.Spoke
import YM.Planned.ATOM_REGULAR_ESTIMATE.Tests


/-! # Coarse-input provider on a bounded use radius

One chart gauge held through any V variation at this station, even on
an equality boundary. Parameterized by exact ordered journeys, including
ONES with root different from gauge origin; no local smallness of the
radius from that other root needed. Cut off only beyond the full
past/future dependence halo actually invoiced elsewhere. No plate promise
about the zero extension itself outside. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Metric Lattice Wilson Pressure RG Tree Next Next.Fluctuations Next.SectorChange
   Exterior Bloch Bid AnalyticBridge.SectorAffine.Offset Push.Uniform Planned.AtomRegular.Foliage
open WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {P : BudgetPoint} {V : Config G c} {g : Site c → G.El} {Y : Support c} {o : Site c} {r l n : ℕ}

def crop (o : Site c) (r : ℕ) (g : Site c → G.El) (V : Config G c) : Directions G c := fun e =>
  if separation o e.1 ≤ r then G.plog (G.mat (gauge g V e)) else 0
abbrev launch (V : Config G c) (o : Site c) (r : ℕ) (g : Site c → G.El) {l : ℕ} (A : Slab G c l) := crop o r g ∘ journey V l A
lemma launch_zero (A : Slab G c l) : launch V o r g A 0=crop o r g V := congrArg (crop o r g) (Planned.AtomRegular.Sample.journey_origin V A)

structure Canvas (P : BudgetPoint) (o : Site c) (r : ℕ) (V : Config G c) (g : Site c → G.El) (n : ℕ) (C : ℝ) : Prop where
  seen : ∀ᶠ W in 𝓝 V, AgreeNear id o r (gauge g W) (increment 1 (crop o r g W))
  germ : ContDiffAt ℝ ω (crop o r g ∘ increment V) 0
  size e : separation o e.1 ≤ r → ‖crop o r g V e‖ ≤ C*P.threshold*(1+separation o e.1)
  ready {j : ℕ} (A : Slab G c j) : ContDiffAt ℝ n (launch V o r g A) 0
  derivatives {l : ℕ} (A : Slab G c l) (p : Site c) : l ≤ n → (∀ i,P.dirBound p (A i)) → ∀ j : ℕ, 1 ≤ j → j ≤ n → ∀ e : Bond c,
    ‖iteratedFDeriv ℝ j (fun t => launch V o r g A t e) 0‖ ≤ if separation o e.1 ≤ r then C*(P.threshold*spine P.power e.1 p)^j else 0

private lemma coordinates (Z : Collar G n) (hn : 1≤n) (hk : Cube.Wire P r Z) (hg : ∀ i : Bond c, separation o i.1 ≤ r → G.chord (gauge g V i) ≤ 4*(P.threshold*(1+separation o i.1))) :
    (∀ᶠ W in 𝓝 V, ∀ i : Bond c,separation o i.1 ≤ r → G.mat (gauge g W i) ∈ ball 1 Z.r) ∧
      ∀ i : Bond c,separation o i.1 ≤ r → ‖crop o r g V i‖ ≤ (Z.count*(4*G.colorScale))*P.threshold*(1+ separation o i.1) := by
  have hc := G.colorScale_pos; have hz := Z.pos
  have he i (hi : separation o (i:Bond c).1 ≤ r) : dist (G.mat (gauge g V i)) 1 ≤ G.colorScale*(4*(P.threshold*(1+separation o i.1))) := by rw [dist_eq_norm,← chord_dist]; exact mul_le_mul_of_nonneg_left (hg i hi) hc.le
  have h i (hi : separation o (i:Bond c).1 ≤ r) : G.mat (gauge g V i)∈ball 1 Z.r := by
    refine mem_ball.mpr ((he i hi).trans_lt (lt_of_le_of_lt ?_ hk.1))
    unfold Cube.moduleBill; have hp := P.threshold_pos
    gcongr ?_*(?_*(?_*?_)); exact (add_le_add_right (show (separation o i.1:ℝ) ≤ r from Nat.cast_le.mpr hi) _).trans
      (le_self_pow₀ (by simp) (by have := P.power_ge; omega))
  have hh : ∀ᶠ W in 𝓝 V, ∀ i:Bond c,separation o i.1 ≤ r → G.mat (gauge g W i) ∈ ball 1 Z.r := by
    apply eventually_all.mpr; intro i; by_cases hi : separation o i.1 ≤ r
    · simp only [hi,true_implies]
      exact (show Continuous (fun W : Config G c => G.mat (gauge g W i)) by unfold Lattice.gauge; fun_prop).continuousAt.eventually (isOpen_ball.mem_nhds (h i hi))
    exact Eventually.of_forall fun _ ht => (hi ht).elim
  refine ⟨hh,fun i hi => ?_⟩
  rw [crop,if_pos hi]
  have hb := (convex_closedBall (1:G.Mat) Z.r).norm_image_sub_le_of_norm_fderiv_le (f:=G.plog) (y:=G.mat (gauge g V i))
    (fun p hp => (Z.log p hp).analytic.differentiableAt (by simp)) (C:=Z.count) (fun p hp => by rw [← norm_iteratedFDeriv_one]; exact (Z.log p hp).norm_le _ hn) (mem_closedBall_self hz.le) (ball_subset_closedBall (h i hi))
  rw [G.plog_one,sub_zero, ← dist_eq_norm] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (he i hi) Z.count_pos.le).trans_eq (by ring))

private lemma canvas_price (Z : Collar G n) (hn : 1≤n) (hk : Cube.Wire P r Z)
    (hg : ∀ i : Bond c, separation o i.1 ≤ r → G.chord (gauge g V i) ≤ 4*(P.threshold*(1+separation o i.1))) : Canvas P o r V g n (Cube.fee Z) := by
  obtain ⟨hh,he⟩ := coordinates Z hn hk hg
  have h0 := Cube.fee_one Z; have hp := P.threshold_pos
  have h₁ := (Cube.stamps G Z).choose_spec
  have seen := hh.self_of_nhds
  refine ⟨hh.mono (fun W h i hi => ?_),contDiffAt_pi.mpr (fun i => ?_),fun i hi => ?_,fun A => contDiffAt_pi.mpr (fun i => ?_),fun {l} A q hl hA j hj hJ i => ?_⟩
  · change separation o i.1 ≤ r at hi; rw [increment,crop, if_pos hi]; exact (mul_one (G.lieExp _)).trans (Z.group _ (ball_subset_closedBall (h i hi))) |>.symm
  · simp only [Function.comp_apply,crop]; split; swap; exact contDiffAt_const
    next hi =>
    let w (z : Directions G c) := G.mat (gauge g (increment V z) i)
    have hq : ContDiff ℝ ω w := by
      simp only [w,Lattice.gauge,increment,G.mat_mul]; exact (contDiff_const.mul ((G.exp_jet.comp (contDiff_apply ..)).mul contDiff_const)).mul contDiff_const
    apply ContDiffAt.comp (f:=w) (g:=G.plog) 0 _ hq.contDiffAt
    unfold w; rw [Work.G07.at_zero_increment]; exact (Z.log _ (ball_subset_closedBall (seen i hi))).analytic
  · refine (he i hi).trans ?_; unfold Cube.fee; rw [mul_comm (4:ℝ)]; gcongr; linarith only [show 1 ≤ Cube.cap Z from h₁.1]
  · simp only [launch,Function.comp_apply,crop]; split; swap; exact contDiffAt_const
    next hi =>
    let w z := G.mat (gauge g (journey V _ A z) i)
    let φ (z : Panels _) := fun j => z j • A j i
    have hw : ContDiff ℝ (n:ℕ∞ω) w := by
      unfold w Lattice.gauge journey; simp_rw [Cube.starts_expanded,G.mat_mul]
      exact ((contDiff_const.mul ((((Cube.starts_diff G _).comp (f:=φ) (by unfold φ; fun_prop)).of_le le_top).mul contDiff_const)).mul contDiff_const)
    apply ContDiffAt.comp (g:=G.plog) (f:=w) 0 _ hw.contDiffAt
    unfold w; rw [Planned.AtomRegular.Sample.journey_origin]; exact ((Z.log _ (ball_subset_closedBall (seen i hi))).analytic).of_le le_top
  simp only [launch,Function.comp_apply,crop]; split; swap; simp
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

theorem primed (h : Healthy P.threshold Y V) (hY : halo (r+1) {o} ⊆ Y) (hc : 2*(r+1)<c.val) (Z : Collar G n) (hn : 1≤n) (hk : Cube.Wire P r Z) :
    ∃ g : Site c → G.El, Canvas P o r V g n (Cube.fee Z) := by
  obtain ⟨g,hg⟩ := Cube.anchored o h P.threshold_pos.le hY hc
  exact ⟨g,canvas_price Z hn hk hg⟩

end YM.PhysicalNext.JointLoad.Heir
