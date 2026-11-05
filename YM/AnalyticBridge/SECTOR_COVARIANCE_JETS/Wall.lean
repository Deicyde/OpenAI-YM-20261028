import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Calc
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Affine

set_option warningAsError false

/-!
# Mixed jets on real curved plaquettes and transport walls

Inserted cutoff of the log increments only for proving estimates (to pass even
infinite sums of coincident path labels through finite-order derivatives). In
the working neighborhood the resulting data agree with the literal SectorChange
definitions. Longer paths: only pay growth from *hit* letters, not untouched
unitaries at those real V. We use FREE_RESOLVENT.Affine.Ceiling tools for that.
-/

set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.Covariance
open Function Filter Lattice Wilson RG Precision Exterior Tree Matrix MeasureTheory
  Pressure Pressure.Tube Bid Next.SectorChange Next.SectorChange.Rows
  Push.SectorMeasure FreeResolvent.TestD FreeResolvent.Affine
open scoped Topology Matrix.Norms.Frobenius ContDiff InnerProductSpace BigOperators Classical

variable {G : Gauge} {c f n : Side} {S : StepData c f} {k : ℕ}

/-- Auxiliary real smooth extension. Real COMMON chart V held fixed. -/
def extendV (V : Config G c) (B : Directions G c) : Config G c := increment V fun i => sleeve G (B i)

def wall (S : StepData c f) (s : Signed) (V : Config G c) (X : Directions G c × Directions G f) : Config G f :=
  pull s 0 (extendV (replica S.ratio (extendV V X.1)) X.2)

def labelFace (S : StepData c f) (s : Signed) (V : Config G c) (p : Cell f) (X : Directions G c × Directions G f) : G.Color :=
  G.curvature (faceValue (wall S s V X) p)

lemma extend_agrees (V : Config G c) {a : Directions G c} (ha : ‖a‖ ≤ 1) : extendV V a=increment V a := by
  funext e; unfold extendV increment
  have he : FreeResolvent.Affine.cuff G (a e) = 1 := by
    apply ContDiffBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall,dist_zero_right]; exact (norm_le_pi_norm a e).trans ha
  simp only [sleeve,he,one_smul]

lemma wall_agrees (S : StepData c f) (s : Signed) (V : Config G c) {B : Directions G c} {a : Directions G f}
    (hb : ‖B‖ ≤ 1) (ha : ‖a‖ ≤ 1) : wall S s V (B,a)=facade S s (increment V B) a := by unfold wall facade; simp only [extend_agrees _ hb,extend_agrees _ ha]

lemma tangent_agrees (S : StepData c f) (s : Signed) (V : Config G c) (p : Cell f)
    (t : Directions G f) {B : Directions G c} (hb : ‖B‖ ≤ 1) :
    upright (labelFace S s V p) t B = plaquetteJet S (increment V B) s p t := by
  unfold upright plaquetteJet
  have hu : (fun y : Directions G f => labelFace S s V p (B,y)) =ᶠ[𝓝 0]
      (fun y => G.curvature (faceValue (facade S s (increment V B) y) p)) := by
    filter_upwards [Metric.closedBall_mem_nhds (0 : Directions G f) zero_lt_one] with y hy
    unfold labelFace; rw [wall_agrees S s V hb (by simpa using hy)]
  rw [hu.fderiv_eq]

private def logDue (G : Gauge) (k : ℕ) : ℝ := (linen_price G k).choose
private lemma logDue_nn (G : Gauge) (k : ℕ) : 0 ≤ logDue G k := (linen_price G k).choose_spec.1

def cents {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) := ‖L‖
lemma cents_nonneg {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) : 0 ≤ cents L := norm_nonneg _

private lemma jacket (V : Config G c) (i : Bond c) : Ceiling k (logDue G k) (fun B => G.mat (extendV V B i)) := by
  simp_rw [extendV,increment,G.mat_mul]
  let L : Directions G c →L[ℝ] G.Color := ContinuousLinearMap.proj i
  let R : G.Mat →L[ℝ] G.Mat := (ContinuousLinearMap.mul ℝ G.Mat).flip (G.mat (V i))
  have ht : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; simpa [L] using norm_le_pi_norm v i)
  have hr : cents (E:=G.Mat) (F:=G.Mat) R ≤ 1 := ContinuousLinearMap.opNorm_le_bound R zero_le_one fun a => by
    change ‖a * _‖ ≤ _
    rw [one_mul]; exact le_of_eq (Gauge.frob_mul_eq _ _ (G.mat_mul_star _))
  have hy := (((linen_price G k).choose_spec.2.pre L (logDue_nn G k) ht le_rfl).post R)
  apply hy.mono
  rw [one_pow, mul_one]; exact mul_le_of_le_one_left (logDue_nn G k) hr

def uniformPatch (G : Gauge) (k : ℕ) :=
  2^k * (‖(ContinuousLinearMap.mul ℝ G.Mat)‖ * logDue G k * max (logDue G k) ‖(1:G.Mat)‖)
lemma uniform_nn (G : Gauge) (k : ℕ) : 0 ≤ uniformPatch G k := by
  have := logDue_nn G k; unfold uniformPatch; positivity

lemma patch_wall (S : StepData c f) (s : Signed) (V : Config G c) (e : Lattice.Step) (x : Site f) :
    Ceiling k (uniformPatch G k) (fun X : Directions G c × Directions G f => G.mat (e.read (wall S s V X) x)) := by
  let U (X : Directions G c × Directions G f) := extendV (replica S.ratio (extendV V X.1)) X.2
  have hn := logDue_nn G k
  have hp (b : Bond f) : Ceiling k (uniformPatch G k) (fun X => G.mat (U X b)) := by
    let F (B) := G.mat (replica S.ratio (extendV V B) b)
    let C := max (logDue G k) ‖(1:G.Mat)‖
    have hc : 0 ≤ C := le_trans hn (le_max_left ..)
    have ht : Ceiling k C F := by
      unfold F replica; split
      · simpa only [G.mat_one] using (Ceiling.ceiling_const (k:=k) (E:=Directions G c) (G.mat 1)).mono (B:=C)
          (show _ ≤ C by rw [G.mat_one]; exact le_max_right ..)
      exact (jacket V _).mono (le_max_left ..)
    let L := ContinuousLinearMap.fst ℝ (Directions G c) (Directions G f)
    let T := (show Directions G f →L[ℝ] G.Color from ContinuousLinearMap.proj b) ∘L
      (ContinuousLinearMap.snd ℝ (Directions G c) (Directions G f))
    have hl : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; simp [L,Prod.norm_def])
    have hT : ‖T‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by intro v; change ‖v.2 b‖ ≤ _; rw [one_mul, Prod.norm_def]; exact ((norm_le_pi_norm v.2 b).trans (le_max_right ‖v.1‖ ‖v.2‖)))
    have hL := ht.pre L hc hl le_rfl
    have hv := (linen_price G k).choose_spec.2.pre T hn hT le_rfl
    rw [one_pow,mul_one] at hL hv
    simp_rw [U,extendV,increment,G.mat_mul]
    -- avoid unfolding inner V on RHS
    exact hv.mul hL (ContinuousLinearMap.mul ℝ G.Mat) hn hc
  have ht (e : Lattice.Step) (x : Site f) : Ceiling k (uniformPatch G k) (fun X => G.mat (e.read (U X) x)) := by
    unfold Lattice.Step.read; split
    · simp_rw [G.mat_inv]; exact star_ceiling (hp _)
    exact hp _
  simp only [wall, Step.pull_read]; exact ht _ _

def wallMoney (G : Gauge) (k : ℕ) (σ : ℝ) := patchMoney G k σ (uniformPatch G k) k
lemma wallMoney_nn (G : Gauge) (k : ℕ) {σ : ℝ} (h : 0<σ) : 0 ≤ wallMoney G k σ := patch_nn G k h (uniform_nn ..) k

lemma walking_wall (k : ℕ) (S : StepData c f) (s : Signed) (V : Config G c) (w : Walk) (x : Site f) {σ : ℝ} (hs : 0<σ) :
    Ceiling k (wallMoney G k σ * Real.exp (σ*w.length)) (fun X => G.mat (travel (wall S s V X) x w)) := by
  let A := uniformPatch G k
  have ha := uniform_nn G k
  have he (b : Lattice.Step) (x : Site f) := patch_wall (k:=k) S s V b x
  constructor
  · exact travel_cd (fun b x => (he b x).smooth) w x
  intro i p hi
  apply list_op (mul_nonneg (wallMoney_nn _ _ hs) (Real.exp_pos _).le)
  intro l v hl hv
  have hh := assembled_jets (p:=p) (fun b x => (he b x).smooth) ha hs
    (fun b x l hg => (he b x).bill ha v hv l hg p) w x l (hl.le.trans hi)
  exact hh.trans (mul_le_mul_of_nonneg_right (patch_le hs ha (hl.le.trans hi)) (Real.exp_pos _).le)

def blade (G : Gauge) : G.Mat →L[ℝ] G.Color := G.projectColor.toContinuousLinearMap ∘L
  ((1/2:ℝ) • ((ContinuousLinearMap.id ℝ G.Mat)-(starL ℝ).toContinuousLinearMap))

def bladeMoney (G : Gauge) (k : ℕ) := cents (E:=G.Mat) (F:=G.Color) (blade G) * (wallMoney G k 1 * Real.exp (1*4))
lemma blade_nn (G : Gauge) (k : ℕ) : 0 ≤ bladeMoney G k := mul_nonneg (cents_nonneg (blade G)) (mul_nonneg (wallMoney_nn _ _ zero_lt_one) (Real.exp_pos _).le)

lemma faces_cap (S : StepData c f) (s : Signed) (V : Config G c) (p : Cell f) (k : ℕ) :
    Ceiling k (bladeMoney G k) (labelFace S s V p) := by
  have h := (walking_wall k S s V (Lattice.square p.2.1.1 p.2.1.2) p.1 zero_lt_one).post (blade G)
  change Ceiling k _ _ at h
  apply h.mono (le_of_eq ?_)
  unfold bladeMoney cents Lattice.square; norm_num
end YM.AnalyticBridge.Covariance
