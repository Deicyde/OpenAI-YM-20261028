import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Motion


set_option warningAsError false


set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

/-!
# Curved fixed-L tests. Jet prices uniform in all periods

We only need arbitrarily small perturbation price here (not `C_L t` rate),
with its fixed-L threshold in the chord size. Input directions count *only*
the stated local patch. Endpoint-sharing choices and generating functions
of usesMin etc unchanged. Q proof transplants the derivative to one
big-enough torus as in Next.FLUCTUATIONS.Prediction, but now facing
Lie increments over a *field*, comparing operator norms. P component
first: can actually bound on entire group (no needs of branches).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.SectorChange.LocalJet
open Function Filter Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix Gaussian
  YM.Pressure YM.Pressure.Tube YM.Pressure.Stores YM.Bid YM.Push.SectorMeasure YM.Push
open YM.Push.SectorMeasure.Oriented SectorChange.Motion NormedSpace
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {c f n : Side} {S : StepData c f}

/-- Neighborhood cost. Overcounts for individual face sites etc. -/
def settle (S : StepData c f) (x : Site c) (r : ℕ) (a : Directions G f) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun e : Bond f => separation x (S.ratio.parent e.1) ≤ r), ‖a i‖
lemma settle_nonneg (S : StepData c f) (x : Site c) (r : ℕ) (a : Directions G f) : 0 ≤ settle S x r a := by
  unfold settle; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
lemma settle_pays (S : StepData c f) (a : Directions G f) (x : Site c) (r : ℕ) {e : Bond f}
    (he : separation x (S.ratio.parent e.1) ≤ r) : ‖a e‖ ≤ settle S x r a :=
  Finset.single_le_sum (fun i _ => norm_nonneg (a i)) (Finset.mem_filter.mpr ⟨Finset.mem_univ e,he⟩)

section face
private abbrev pins (p : Cell f) : Fin 4 → Bond f :=
  let x := p.1; let i := p.2.val.1; let j := p.2.val.2
  ![(x,i),(x+Lattice.step i,j),(x+Lattice.step j,i),(x,j)]
private def readSet (p : Cell f) : Directions G f →L[ℝ] LogArray G (Fin 4) :=
  (LinearMap.pi fun i => LinearMap.proj (pins p i)).toContinuousLinearMap
private def square (u : LinkArray G (Fin 4)) (a : LogArray G (Fin 4)) :=
  G.curvature (release u a 0 * release u a 1 * ((release u a 2)⁻¹ * (release u a 3)⁻¹))

private lemma square_eq (p : Cell f) (u : Config G f) : pTest u p = square (u ∘ pins p) ∘ readSet p := by
  have h (x : Site f) (i j : Axis) : x + Lattice.step i + Lattice.step j - Lattice.step i = x + Lattice.step j := by abel
  have he (x : Site f) (i j : Axis) : x + Lattice.step i + Lattice.step j + (- Lattice.step i) = x + Lattice.step j := by abel
  funext a; unfold pTest faceValue Lattice.square travel square Function.comp
  simp only [travel, Step.vec_pos, Step.vec_neg, Step.pos_read, Step.neg_read, h,he,add_sub_cancel_right]
  have hx (i : Fin 4) : readSet p (G:=G) a i = a (pins p i) := rfl
  simp [pins,increment,release,hx,mul_assoc]

-- mat version on all possibly nonunitary links

-- make reducible for instances
private def scene (x : (Fin 4 → G.Mat) × LogArray G (Fin 4)) : G.Color :=
  let v := fun (i : Fin 4) => G.mat (G.lieExp (x.2 i))*x.1 i
  let z := v 0 * v 1 * (star (v 2) * star (v 3))
  G.projectColor ((1/2:ℝ) • (z-star z))

private lemma scene_square (u : LinkArray G (Fin 4)) : square u = fun a => scene (fun i => G.mat (u i), a) := by
  funext a
  unfold square scene Gauge.curvature release
  simp only [G.mat_inv,G.mat_mul]

private lemma scene_smooth : ContDiff ℝ ω (scene (G:=G)) := by
  let W := (Fin 4 → G.Mat) × LogArray G (Fin 4)
  have he (i : Fin 4) : ContDiff ℝ ω (fun x : W => G.mat (G.lieExp (x.2 i))*x.1 i) := by
    apply (G.exp_jet.comp ((contDiff_apply ℝ G.Color _).comp contDiff_snd)).mul
    exact (contDiff_apply ℝ G.Mat _).comp contDiff_fst
  let B := show G.Mat ≃L[ℝ] G.Mat from starL ℝ
  have hb (i) := B.contDiff.comp (he i)
  let v (i : Fin 4) (x : W) := G.mat (G.lieExp (x.2 i))*x.1 i
  have hs : ContDiff ℝ ω (fun x => v 0 x * v 1 x * (B (v 2 x) * B (v 3 x))) :=
    ((he _).mul (he _)).mul ((hb _).mul (hb _))
  exact G.projectColor.toContinuousLinearMap.contDiff.comp ((hs.sub (B.contDiff.comp hs)).const_smul (1/2:ℝ))

private lemma square_smooth (u : LinkArray G (Fin 4)) : ContDiff ℝ ω (square u) := by
  rw [scene_square]; exact scene_smooth.comp (contDiff_const.prodMk contDiff_id)

private lemma square_deriv_cont : Continuous (fun u : LinkArray G (Fin 4) => fderiv ℝ (square u) 0) := by
  have hg : Continuous (fun u : Fin 4 → G.Mat => fderiv ℝ (fun y : LogArray G (Fin 4) => scene (u,y)) 0) :=
    (ContDiff.fderiv (f:=fun u y => scene (u,y)) (g:=fun _ : Fin 4 → G.Mat => (0:LogArray G (Fin 4))) (m:=ω) (n:=ω)
      scene_smooth contDiff_const (by simp)).continuous
  let L := fun u : LinkArray G (Fin 4) => fun i => G.mat (u i)
  have hl : Continuous L := continuous_pi fun i => G.continuous_mat.comp (continuous_apply i)
  simp_rw [scene_square]
  exact hg.comp hl

private lemma read_size (S : StepData c f) (p : Cell f) (i : Fin 4) :
    separation (S.ratio.parent p.1) (S.ratio.parent (pins p i).1) ≤ 1 := by
  have h x v := Work.E03.parent_step S x v
  fin_cases i
  · exact (separation_self _).trans_le (Nat.zero_le _)
  · exact h _ _
  · exact h _ _
  · exact (separation_self _).trans_le (Nat.zero_le _)

lemma face_smooth (U : Config G f) (p : Cell f) : ContDiff ℝ ω (pTest U p) := by
  rw [square_eq]; exact (square_smooth _).comp (readSet p).contDiff

lemma face_global (G : Gauge) : ∃ C : ℝ, 0 < C ∧ ∀ {c f : Side} (S : StepData c f) (p : Cell f)
    (U : Config G f) (a : Directions G f), ‖fderiv ℝ (pTest U p) 0 a‖ ≤ C * settle S (S.ratio.parent p.1) 1 a := by
  obtain ⟨C,hC⟩ := (isCompact_range (square_deriv_cont (G:=G)).norm).bddAbove
  have he (u : LinkArray G (Fin 4)) : ‖fderiv ℝ (square u) 0‖ ≤ C := hC ⟨u,rfl⟩
  have hc := (norm_nonneg _).trans (he 1)
  refine ⟨1+C, by linarith,?_⟩
  intro c f S p U a
  rw [square_eq, fderiv_comp _ ((square_smooth _).differentiable (by simp) _) (readSet _).differentiableAt, map_zero, (readSet _).fderiv,ContinuousLinearMap.comp_apply]
  refine ((fderiv ℝ (square _) 0).le_opNorm _).trans (mul_le_mul ((he _).trans (by linarith)) ?_ (norm_nonneg _) (by linarith))
  exact (pi_norm_le_iff_of_nonneg (settle_nonneg ..)).mpr fun i => settle_pays _ _ _ _ (read_size S p i)

lemma face_comparison (G : Gauge) {ε : ℝ} (he : 0<ε) : ∃ δ : ℝ, 0 < δ ∧
    ∀ {c f : Side} (S : StepData c f) (p : Cell f) (U : Config G f),
    (∀ e : Bond f, separation (S.ratio.parent p.1) (S.ratio.parent e.1) ≤ 1 → G.chord (U e) ≤ δ) →
    ∀ a : Directions G f, ‖fderiv ℝ (pTest U p) 0 a - fderiv ℝ (pTest 1 p) 0 a‖ ≤ ε * settle S (S.ratio.parent p.1) 1 a := by
  let F := fun u : LinkArray G (Fin 4) => fderiv ℝ (square u) 0
  have hi := (square_deriv_cont (G:=G)).continuousAt.preimage_mem_nhds (x:=1) (ball_mem_nhds (F 1) he)
  -- use Pi-closedball and chord/frob relation
  obtain ⟨r,hr,h⟩ := nhds_basis_closedBall.mem_iff.mp hi
  refine ⟨r/G.colorScale, div_pos hr G.colorScale_pos,?_⟩
  intro c f S p U hv a
  let u : LinkArray G (Fin 4) := U ∘ pins p
  have hs (i : Fin 4) : dist (u i) (1:G.El) ≤ r := by
    change dist (G.mat (u i)) (G.mat 1) ≤ r
    rw [G.mat_one,dist_eq_norm,← Fluctuations.chord_dist,mul_comm]
    exact (le_div_iff₀ G.colorScale_pos).mp (hv _ (read_size S p i))
  have ht : ‖F u - F 1‖ ≤ ε := by
    rw [← dist_eq_norm]
    refine le_of_lt (mem_ball.mp (h (Metric.mem_closedBall.mpr ((dist_pi_le_iff hr.le).mpr hs))))
  simp_rw [square_eq, fderiv_comp _ ((square_smooth _).differentiable (by simp) _) (readSet _).differentiableAt, map_zero, (readSet _).fderiv,ContinuousLinearMap.comp_apply]
  change ‖F u (readSet p a) - F 1 (readSet p a)‖ ≤ _
  refine ((F u - F 1).le_opNorm _).trans (mul_le_mul ht ?_ (norm_nonneg _) he.le)
  exact (pi_norm_le_iff_of_nonneg (settle_nonneg ..)).mpr fun i => settle_pays _ _ _ _ (read_size S p i)
end face
end YM.Next.SectorChange.LocalJet
