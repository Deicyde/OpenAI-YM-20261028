import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.NoHole
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Rebased
import YM.Next.ROTATIONS.Response

/-!
# Actual first-vertical face jets on true backgrounds, before pricing ℓ_R

Coarse and fine relative fields varied jointly, all signed channels. No
sector smoothness on guard decisions asserted. Exact locality at all inputs
with a constant-size stencil, period-independent costs at arbitrary base.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Selected
open Lattice Wilson RG Precision Exterior Tree Function Filter Topology Bloch Next.SectorChange Next.Fluctuations
  YM.Pressure YM.Pressure.Stores FreeResolvent Affine Mark TestD Push.Uniform
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : ℕ}

def landscape (S : StepData c f) (V : Config G c) (B : Vec G c 1) := replica S.ratio (increment V (paint G c B))

def forward (S : StepData c f) (V : Config G c) (z : pair G c f) := increment (landscape S V z.1) (paint G f z.2)

def petals (S : StepData c f) (V : Config G c) (s : Signed) (z : pair G c f) := NoHole.faceRow S s (increment V (paint G c z.1)) z.2

lemma petal_apply (S : StepData c f) (V : Config G c) (s : Signed) (z : pair G c f) (j : tile G f) :
    petals S V s z j = G.curvature (faceValue (pull s 0 (forward S V z)) (j.1,plaqEquiv.symm j.2.1)) j.2.2 := rfl

lemma landscape_local (S : StepData c f) (V : Config G c) (o : Site c) (R : ℕ) (z : pair G c f) :
    AgreeNear S.ratio.parent o R (landscape S V (stopAt S o R z).1) (landscape S V z.1) := by
  intro i hi
  unfold landscape replica; split
  · rfl
  rename_i h
  unfold increment; congr 2
  ext e
  change (if separation o (S.ratio.parent i.1) ≤ R then _ else 0) = _; rw [if_pos hi]; rfl

lemma forward_local (S : StepData c f) (V : Config G c) (o : Site c) (R : ℕ) (z : pair G c f) :
    AgreeNear S.ratio.parent o R (forward S V (stopAt S o R z)) (forward S V z) := by
  intro i hi
  unfold forward increment
  rw [landscape_local S V o R z i hi]
  congr 2
  ext e
  change (if separation o (S.ratio.parent i.1) ≤ R then _ else 0) = _; rw [if_pos hi]; rfl

lemma petals_local (S : StepData c f) (V : Config G c) (s : Signed) (z : pair G c f) (i : tile G f) :
    petals S V s (stopAt S (named S s i) 4 z) i = petals S V s z i := by
  let w := square (plaqEquiv.symm i.2.1).val.1 (plaqEquiv.symm i.2.1).val.2
  have he : faceValue (pull s 0 (forward S V (stopAt S (named S s i) 4 z))) (i.1,plaqEquiv.symm i.2.1) = _ := calc
    _ = travel (forward S V (stopAt S (named S s i) 4 z)) (affine s 0 i.1) (w.map (·.rotate s)) := travel_pull ..
    _ = travel (forward S V z) (affine s 0 i.1) (w.map (·.rotate s)) :=
      travel_near S.ratio.parent (Work.E03.parent_step S) _ _ _ _ 4 (by simp [w,square]) (forward_local S V _ 4 z)
    _ = faceValue (pull s 0 (forward S V z)) (i.1,plaqEquiv.symm i.2.1) := (travel_pull ..).symm
  rw [petal_apply,he,← petal_apply]

section allows
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {y : E} {C K : ℝ} {U V : E → G.El}

def mulFee (G : Gauge) (k : ℕ) (C K : ℝ) := 2^k * ‖ContinuousLinearMap.mul ℝ G.Mat‖ * C * K
lemma mul_fee_nn (h : 0 ≤ C) (he : 0 ≤ K) : 0 ≤ mulFee G k C K := by unfold mulFee; positivity

lemma mul_pay (h : Allows k (fun y => G.mat (U y)) y C) (he : Allows k (fun y => G.mat (V y)) y K) :
    Allows k (fun y => G.mat (U y * V y)) y (mulFee G k C K) := by
  simp_rw [G.mat_mul]; exact h.bilinear (ContinuousLinearMap.mul ℝ G.Mat) he le_rfl

lemma inv_pay (h : Allows k (fun y => G.mat (U y)) y C) : Allows k (fun y => G.mat ((U y)⁻¹)) y C := by
  let L := (starL ℝ : G.Mat ≃L[ℝ] G.Mat).toContinuousLinearMap
  have he := h.linear (show G.Mat →L[ℝ] G.Mat from L) (K:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [one_mul]; exact (norm_star x).le)
  rw [one_mul] at he
  simp only [Gauge.mat_inv]; exact he

lemma read_pay {U : E → Config G f} (h : ∀ e, Allows k (fun y => G.mat (U y e)) y C) (x : Site f) (s : Step) :
    Allows k (fun y => G.mat (s.read (U y) x)) y C := by
  unfold Step.read; split
  · exact inv_pay (h _)
  exact h _

def tripFee (G : Gauge) (k : ℕ) (C : ℝ) : ℕ → ℝ
  | 0 => ‖(1:G.Mat)‖
  | n+1 => mulFee G k C (tripFee G k C n)
lemma trip_nn (h : 0 ≤ C) (n : ℕ) : 0 ≤ tripFee G k C n := by
  induction n with
  | zero => exact norm_nonneg _
  | succ n ih => exact mul_fee_nn h ih
lemma trip_pay {U : E → Config G f} (h : ∀ e, Allows k (fun y => G.mat (U y e)) y C) (x : Site f) (w : Walk) :
    Allows k (fun y => G.mat (travel (U y) x w)) y (tripFee G k C w.length) := by
  induction w generalizing x with
  | nil => exact allows_const _ le_rfl
  | cons s l ih => exact mul_pay (read_pay h x s) (ih _)
end allows

lemma forward_pay (G : Gauge) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {c f : Side} (S : StepData c f) (V : Config G c) (i : Bond f),
    Allows k (fun z => G.mat (forward S V z i)) 0 C := by
  obtain ⟨N,hN,he⟩ := exists_allows (f:=fun v => G.mat (G.lieExp v)) (s:={(0:G.Color)}) isCompact_singleton (fun _ _ => G.exp_jet.contDiffAt) k
  let D := composeCost k N (filePrice G)
  let M := max ‖(1:G.Mat)‖ (mulFee G k D ‖(1:G.Mat)‖)
  have hD : 0 ≤ D := by have := file_pos G; unfold D composeCost; positivity
  refine ⟨mulFee G k D M,mul_fee_nn hD ((norm_nonneg _).trans (le_max_left ..)),?_⟩
  intro c f S V i
  have h0 := he 0 (Set.mem_singleton _)
  have hh (e) : Allows k (fun z : pair G c f => G.mat (G.lieExp (paint G c z.1 e))) 0 D := by
    refine Allows.comp (C:=filePrice G) (K:=N) (f:=fun z : pair G c f => paint G c z.1 e) (g:=fun a => G.mat (G.lieExp a)) ?_ ?_
    · rw [Prod.fst_zero,map_zero, Pi.zero_apply]; exact h0
    have hx := (front_paint G c f k).linear _ (allows_at (E:=G.Color) e)
    rw [one_mul] at hx; exact hx
  refine mul_pay ?_ ?_
  · refine Allows.comp (C:=filePrice G) (K:=N) (f:=fun z : pair G c f => paint G f z.2 i) (g:=fun a => G.mat (G.lieExp a)) ?_ ?_
    · rw [Prod.snd_zero,map_zero,Pi.zero_apply]; exact h0
    have hx := (rear_paint G c f k).linear _ (allows_at (E:=G.Color) i)
    rw [one_mul] at hx; exact hx
  unfold landscape replica; split
  · exact allows_const _ (le_max_left ..)
  refine Allows.mono (mul_pay (hh _) (allows_const _ ?_)) (le_max_right ..)
  simpa only [one_mul] using (Gauge.frob_mul_eq (1:G.Mat) _ (G.mat_mul_star (V _))).le

def petalFee (G : Gauge) (k : ℕ) (C : ℝ) := G.colorScale⁻¹ * tripFee G k C 4
lemma petals_pay (G : Gauge) (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ {c f : Side} (S : StepData c f) (V : Config G c)
    (s : Signed) (i : tile G f), Allows k (fun z => petals S V s z i) 0 C := by
  obtain ⟨C,hC,hv⟩ := forward_pay G k
  refine ⟨petalFee G k C,mul_nonneg (inv_nonneg.mpr G.colorScale_pos.le) (trip_nn hC _),?_⟩
  intro c f S V s i
  let U (z : pair G c f) := pull s 0 (forward S V z)
  have hU (e : Bond f) : Allows k (fun y => G.mat (U y e)) 0 C := read_pay (hv S V) ..
  let p := plaqEquiv.symm i.2.1
  have hh := (((trip_pay hU i.1 (square p.val.1 p.val.2)).linear G.projectColor.toContinuousLinearMap (K:=G.colorScale⁻¹) (ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr G.colorScale_pos.le) fun x => by rw [inv_mul_eq_div]; exact G.project_norm x)).linear _ (tint_size (G:=G) i.2.2))
  rw [one_mul] at hh
  simp_rw [petal_apply,curvature_project]
  exact hh
end YM.SelectedOrderedKernels.Selected
