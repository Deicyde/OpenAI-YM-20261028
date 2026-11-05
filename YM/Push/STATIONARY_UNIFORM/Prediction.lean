import YM.Push.STATIONARY_UNIFORM.FrameBall

/-!
# Predictors with shared tags on the stationary ball

The bonds read the actual site frame in TWO places. No introduction of
independent connector data, no differentiating a hard flag. All tags ignored
on the same ball, all kernel tests proved strictly, use real G coordinates.
Still polynomial costs (not the sharp E estimate for *weighted-centered* jets).
-/

set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Pressure Gauge
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge} {c f : Side} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : E → Config G f} {n : ℕ} {K C D δ W r : ℝ}

/- uniform chart estimate, no need to assume from LocalRatio -/
def FocusReceipt (G : Gauge) (n : ℕ) (K R : ℝ) := 0<R ∧ ∀ X : G.Mat, ‖X-1‖ < R →
  Allows n (fun x => G.mat (G.focus x)) X K ∧ ∀ u, G.Nearest u X → u=G.focus X

lemma focus_receipt (G : Gauge) (n : ℕ) : ∃ K R : ℝ, 0<K ∧ FocusReceipt G n K R := by
  have he : ∀ᶠ X : G.Mat in 𝓝 1, ContDiffAt ℝ ω (fun x => G.mat (G.focus x)) X := G.focus_diff.eventually (by simp)
  -- pin exact Frobenius metric
  -- often need helpers for unbundled topology (cf. Path.lean)
  obtain ⟨R,hR,h⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (he.and G.nearest_is_focus)
  obtain ⟨K,hK,hk⟩ := exists_allows (isCompact_closedBall (1:G.Mat) R) (fun x hx => (h hx).1) n
  refine ⟨K+1,R,by positivity, hR,fun X hx => ?_⟩
  have hx' : X∈closedBall (1:G.Mat) R := by rw [mem_closedBall,dist_eq_norm]; exact hx.le
  exact ⟨(hk _ hx').mono (le_add_of_nonneg_right zero_le_one),(h hx').2⟩

section Main
variable (S : StepData c f)

def hatsCost (P : Patch) (G : Gauge) (n : ℕ) (K C : ℝ) := composeCost n K (implicitCost 1 (scoreCost P G (n+1) K C) (rootGap P/2)⁻¹ n)

def connectorCost (P : Patch) (G : Gauge) (n : ℕ) (K C : ℝ) : ℝ :=
  let F := hatsCost P G n K C
  2^n * (2^n*F*travelCost G n P.L.val C)*F

def connectorMove (P : Patch) (G : Gauge) (C : ℝ) : ℝ :=
  let J := alignCost P * Inputs.pathChange G P C
  2*J + P.L.val * Inputs.variation G C

def predictionRadius (P : Patch) (G : Gauge) (Q : KernelChoices) (n : ℕ) (K C D δ r : ℝ) :=
  let F := connectorMove P G C
  min (frameRadius P G (n+1) K C D δ Q) (min (Real.sqrt Q.predictor_cut / F) (r/(G.colorScale*F)))

lemma connectorMove_pos (P : Patch) (G : Gauge) {C : ℝ} (h : 0 ≤ C) : 0 < connectorMove P G C := by
  have hh := Inputs.path_pos P G h
  have he := align_pos P
  have ha : 0 ≤ Inputs.variation G C := div_nonneg h G.colorScale_pos.le
  unfold connectorMove; positivity

lemma prediction_radius_pos (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (hF : FocusReceipt G n W r) :
    0 < predictionRadius S.patch G S.kernel n K C D δ r := by
  have he := frame_radius_pos S.patch hU hK (by omega) (0:Site f) hL S.kernel
  have hs := connectorMove_pos S.patch G hU.2.1
  exact lt_min he (lt_min (div_pos (Real.sqrt_pos.mpr S.kernel.predictor_cut_pos) hs) (div_pos hF.1 (mul_pos G.colorScale_pos hs)))

def averageX (P : Patch) (Y : P.Points → G.El) := ∑ i, P.weight i • G.mat (Y i)

lemma averageX_within (P : Patch) (Y : P.Points → G.El) {M : ℝ} (h : ∀ i, G.chord (Y i) ≤ M) :
    ‖averageX P Y-1‖ ≤ G.colorScale*M := by
  have he : averageX P Y - 1 = ∑ i, P.weight i • (G.mat (Y i)-1) := by simp only [averageX,smul_sub,Finset.sum_sub_distrib, ← Finset.sum_smul,P.weight_sum,one_smul]
  rw [he]
  apply le_trans (norm_sum_le ..)
  calc
    _ ≤ ∑ i, P.weight i*(G.colorScale*M) := Finset.sum_le_sum fun i _ => by
      rw [norm_smul,Real.norm_of_nonneg (P.weight_nonneg i), ← chord_dist]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h i) G.colorScale_pos.le) (P.weight_nonneg _)
    _ = _ := by rw [← Finset.sum_mul,P.weight_sum,one_mul]

lemma frame_comparison (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (frameRadius S.patch G (n+1) K C D δ S.kernel))
    (t : S.SitesChoice) (y : Site c) :
    let h := S.frames (U x) t y; let P := S.patch; let r := S.ratio.embed y
    h = P.frameFromCoordinates G (branchLog P r U x) ∧
      ∀ i, G.chord (h i) ≤ (alignCost P * Inputs.pathChange G P C)*‖x‖ := by
  have he := selects S.patch hU hK (by omega) hL hx (r:=S.ratio.embed y)
  let q := S.patch.selected (expandAt (S.ratio.embed y) (U x)); have hq := (S.patch.min_exists (expandAt (S.ratio.embed y) (U x))).choose_spec
  have ht : S.frames (U x) t y=q := if_pos he.1
  dsimp only; rw [ht]; refine ⟨((he.2 q hq).1.1).symm,fun i => ?_⟩
  have hh : ‖x‖ ≤ 1 := le_trans (show ‖x‖ ≤ _ from (show ‖x‖ < frameRadius S.patch G (n+1) K C D δ S.kernel by simpa using hx).le)
    (le_trans (min_le_left ..) (min_le_left ..))
  rw [mul_assoc]; exact cluster_root S.patch hq (Inputs.closes S.patch hU (by omega) hh) i

lemma connector_within (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (frameRadius S.patch G (n+1) K C D δ S.kernel))
    (t : S.SitesChoice) (b : Bond c) (i : S.patch.Points) :
    G.chord (S.connector (U x) t b i) ≤ connectorMove S.patch G C * ‖x‖ := by
  have h (y : Site c) := (frame_comparison S hU hn hK hL x hx t y).2 i
  have hh : ‖x‖ ≤ 1 := le_trans (show ‖x‖ ≤ frameRadius S.patch G (n+1) K C D δ S.kernel by exact (show ‖x‖ < frameRadius S.patch G (n+1) K C D δ S.kernel by simpa using hx).le)
    (le_trans (min_le_left ..) (min_le_left ..))
  unfold StepData.connector; rw [travel_at]; apply (G.chord_triangle _ _).trans; rw [G.chord_inv]
  apply (add_le_add ((G.chord_triangle _ _).trans (add_le_add (h _) (travel_chord (U x) _ _ _ (Inputs.chord hU (by omega) hh)))) (h _)).trans_eq
  rw [List.length_replicate]; unfold connectorMove; ring

lemma uses_bond (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (predictionRadius S.patch G S.kernel n K C D δ r))
    (t : S.Choices) (b : Bond c) :
    let Y := S.connector (U x) t.1 b
    S.patch.usesBest S.kernel Y ∧ ‖averageX _ Y-1‖ < r := by
  let Y := S.connector (U x) t.1 b
  let L := S.kernel.predictor_cut
  let J := connectorMove S.patch G C
  have he : x∈ball (0:E) (frameRadius S.patch G (n+1) K C D δ S.kernel) := ball_subset_ball (min_le_left ..) hx
  have ht (i) : G.chord (Y i) ≤ J*‖x‖ := connector_within S hU hn hK hL x he t.1 b i
  have hp := averageX_within S.patch Y ht
  have hy := connectorMove_pos S.patch G hU.2.1
  have hz : ‖x‖ < min (Real.sqrt L / J) (r/(G.colorScale*J)) := lt_of_lt_of_le
    (show ‖x‖ < predictionRadius S.patch G S.kernel n K C D δ r by simpa using hx) (min_le_right ..)
  rw [lt_min_iff] at hz
  have hv : 0<L:=S.kernel.predictor_cut_pos
  constructor
  · apply lt_of_le_of_lt ((S.patch.bond_min _).choose_spec 1)
    let a := J*‖x‖; change S.patch.bondCost Y 1 < L
    have ha : 0≤a := mul_nonneg hy.le (norm_nonneg _)
    calc
      _ ≤ ∑ i, S.patch.weight i * (a^2/2) := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (price_of_chord (Y i * 1⁻¹) (by simpa using ht i)) (S.patch.weight_nonneg _)
      _ = a^2/2 := by rw [← Finset.sum_mul,S.patch.weight_sum,one_mul]
      _ < _ := by
        have ht : a < Real.sqrt L := by unfold a; rw [mul_comm]; exact (lt_div_iff₀ hy).1 hz.1
        have h := pow_le_pow_left₀ ha ht.le 2; rw [Real.sq_sqrt hv.le] at h; linarith
  apply hp.trans_lt
  have h := (lt_div_iff₀ (mul_pos G.colorScale_pos hy)).1 hz.2
  change ‖x‖ * (G.colorScale*J)<r at h; linarith

lemma picked_bond (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (hF : FocusReceipt G n W r) (x : E) (hx : x∈ball 0 (predictionRadius S.patch G S.kernel n K C D δ r))
    (t : S.Choices) (b : Bond c) : S.prediction (U x) t b = G.focus (averageX S.patch (S.connector (U x) t.1 b)) := by
  obtain ⟨he,hp⟩ := uses_bond S hU hn hK hL x hx t b
  unfold StepData.prediction Patch.predict; rw [if_pos he]
  exact (hF.2 _ hp).2 _ ((Branch.min_iff _ S.patch.weight_sum _ _).2 (S.patch.bond_min _).choose_spec)

lemma picked_tags (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (predictionRadius S.patch G S.kernel n K C D δ r)) (t t' : S.Choices) :
    S.prediction (U x) t = S.prediction (U x) t' := by
  have ht y (p : S.Choices) := (frame_comparison S hU hn hK hL x (ball_subset_ball (min_le_left ..) hx) p.1 y).1
  have he b p : S.prediction (U x) p b=S.patch.best (S.connector (U x) p.1 b) := if_pos (uses_bond S hU hn hK hL x hx p b).1
  funext b; rw [he,he]
  apply congr_arg S.patch.best; funext i; simp only [StepData.connector,ht]

variable [FiniteDimensional ℝ E]

lemma frame_pay (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (frameRadius S.patch G (n+1) K C D δ S.kernel))
    (t : S.SitesChoice) (y : Site c) (i : S.patch.Points) : Allows n (fun x => G.mat (S.frames (U x) t y i)) x (hatsCost S.patch G n K C) := by
  let P := S.patch
  let q := branchLog P (S.ratio.embed y) U
  have hq : ‖q x‖ ≤ 1 := by
    have ht := ((selects P hU hK (by omega) hL (r:=S.ratio.embed y) hx).2 _
      (P.min_exists _).choose_spec).2.1
    apply le_trans (show ‖q x‖ < hilbertRadius P G (n+1) K C by simpa [q,branchLog,Patch.selected] using ht).le (min_le_left ..)
  have hp := Allows.linear _ (branch_jets P hU hK hn hL hx (r:=S.ratio.embed y)) (read_short _ G i)
  rw [one_mul] at hp
  let w (x) := readLog P i (q x)
  have hw : ‖w x‖ ≤ 1 := ((readLog P i).le_opNorm _).trans (mul_le_one₀ (read_short _ G i) (norm_nonneg _) hq)
  apply Allows.germ (((hK _ hw).order (Nat.le_succ n)).comp (f:=w) hp)
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz; rw [(frame_comparison S hU hn hK hL _ hz t y).1,frame_read]

lemma connector_pay (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (x : E) (hx : x∈ball 0 (frameRadius S.patch G (n+1) K C D δ S.kernel))
    (t : S.SitesChoice) (b : Bond c) (i : S.patch.Points) :
    Allows n (fun x => G.mat (S.connector (U x) t b i)) x (connectorCost S.patch G n K C) := by
  have hh : ‖x‖ ≤ 1 := le_trans (show ‖x‖ ≤ _ from (show ‖x‖ < frameRadius S.patch G (n+1) K C D δ S.kernel by simpa using hx).le)
    (le_trans (min_le_left ..) (min_le_left ..))
  have h (y : Site c) := frame_pay S hU hn hK hL x hx t y i
  simp_rw [StepData.connector,travel_at]
  exact ((h _).times (f:=fun x => _) (g:=fun x => _) (travel_jets (U:=U) (fun j => (hU.2.2 j x hh).order (Nat.le_succ n)) _ (List.length_replicate.le))).times
    (f:=fun x => _) (g:=fun x => _) ((h _).inverse (f:=fun x => _))

lemma prediction_pay (hU : Inputs U (n+1) C) (hn : 2 ≤ n) (hK : ExpReceipt G (n+1) K)
    (hL : LogReceipt G D δ) (hF : FocusReceipt G n W r) (x : E) (hx : x∈ball 0 (predictionRadius S.patch G S.kernel n K C D δ r))
    (t : S.Choices) (b : Bond c) : Allows n (fun x => G.mat (S.prediction (U x) t b)) x (composeCost n W (connectorCost S.patch G n K C)) := by
  have he (i) := (connector_pay S hU hn hK hL x (ball_subset_ball (min_le_left ..) hx) t.1 b i).smul (S.patch.weight i)
  let m (x) := averageX S.patch (S.connector (U x) t.1 b)
  have hm : Allows n m x (connectorCost S.patch G n K C) := by
    have hs := allows_sum (s:=Finset.univ) (fun i _ => he i)
    simp_rw [abs_of_nonneg (S.patch.weight_nonneg _),← Finset.sum_mul,S.patch.weight_sum,one_mul] at hs
    exact hs
  apply Allows.germ (((hF.2 _ (uses_bond S hU hn hK hL x hx t b).2).1).comp (f:=m) hm)
  filter_upwards [isOpen_ball.mem_nhds hx] with z hz; rw [picked_bond S hU hn hK hL hF z hz]
end Main
end YM.Push.Uniform
