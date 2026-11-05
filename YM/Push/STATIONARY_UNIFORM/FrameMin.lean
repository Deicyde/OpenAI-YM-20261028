import YM.Next.FLUCTUATIONS.Charts
import YM.Push.STATIONARY_UNIFORM.FrameScore


/-!
# The minimizers really are in these balls

Quantitatively with preselected gauge-chart costs. Work in full physical
configuration, ties in tags harmless on this actual branch. Uniform in the
number of blocks. Does not look at any gas or masks.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Uniform
open Lattice Wilson RG Precision Pressure Gauge
open Next.Fluctuations Filter Function Set Metric
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace Classical

variable {G : Gauge}

section Compare

variable (P : Patch) {U : CoverConfig G} {r C δ D : ℝ} {h : P.Frame G}

lemma average_le_const {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, f i ≤ r) : Patch.average f ≤ r := by
  have hm : 0 < (Fintype.card ι:ℝ) := by positivity
  apply (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (g:=fun _ => r) (fun i _ => hf i)) (show 0 ≤ (Fintype.card ι:ℝ)⁻¹ by positivity)).trans
  simp [hm.ne']

lemma point_le_average {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ (Fintype.card ι:ℝ)*Patch.average f := by
  haveI := Nonempty.intro i; have hm : 0 < (Fintype.card ι:ℝ) := by positivity
  unfold Patch.average; rw [mul_inv_cancel_left₀ hm.ne']
  exact Finset.single_le_sum (fun i _ => hf i) (Finset.mem_univ i)

lemma average_nonneg' {ι : Type*} [Fintype ι] (f : ι → ℝ) (h : ∀ i, 0≤f i) : 0 ≤ Patch.average f :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => h i)

lemma price_of_chord (v : G.El) (h : G.chord v ≤ r) : G.price v ≤ r^2/2 := by
  have he := G.chord_price v
  have hh := pow_le_pow_left₀ (G.chord_nonneg v) h 2
  linarith

def ClosePaths (U : CoverConfig G) (r : ℝ) := ∀ (i j : P.Points) (l : Lattice.Order),
    G.chord (travel U i.val (route i.val j.val l)) ≤ r

lemma minimizing_used (h : ClosePaths P U r) (K : KernelChoices) (hr : 3*r < K.frame_cut) : P.usesMin K U := by
  intro k l x v
  unfold Patch.via Patch.axial
  apply lt_of_le_of_lt (G.chord_triangle _ _) (lt_of_le_of_lt _ hr); rw [G.chord_inv]
  have hh (i j : P.Points) := h i j l
  apply (add_le_add ((G.chord_triangle _ _).trans (add_le_add (h P.center x k) (hh x v))) (h P.center v k)).trans
  linarith

-- Charge by one term against whole average, not the stronger L powers needed in centering.
def alignCost := 1 + (points P)^2 * (Fintype.card Lattice.Order:ℝ)
lemma align_pos : 0 < alignCost P := by unfold alignCost; positivity

lemma cluster_root (hm : P.minimizing U h) (hr : ClosePaths P U r) (i : P.Points) :
    G.chord (h i) ≤ alignCost P*r := by
  have hx : P.score U h ≤ r^2/2 := (hm.2 1 rfl).trans (average_le_const _ fun i => average_le_const _ fun j => average_le_const _ fun l =>
    price_of_chord _ (by simpa [Patch.via] using hr i j l))
  let q (i j : P.Points) (l : Lattice.Order) := G.price (P.via h U i j l)
  have hq (i j l) : 0 ≤ q i j l := (G.price_range _).1
  let m := (Fintype.card Lattice.Order:ℝ); let p := points P
  have hp : 1 ≤ p := points_ge _; have hO : 1 ≤ m := by unfold m; exact_mod_cast (Fintype.card_pos (α:=Lattice.Order))
  have ht : q i P.center 1 ≤ p^2*m*(r^2/2) := calc
    _ ≤ m * Patch.average (q i P.center) := point_le_average _ (hq i P.center) _
    _ ≤ m * (p * Patch.average (fun j => Patch.average (q i j))) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); exact point_le_average _ (fun j => average_nonneg' _ (hq i j)) _
    _ ≤ m * (p * (p * P.score U h)) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (point_le_average
      (fun i => Patch.average (fun j => Patch.average (q i j))) (fun i => average_nonneg' _ fun j => average_nonneg' _ (hq i j)) _) (by linarith)) (by linarith)
    _ = p^2*m*P.score U h := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hx (mul_nonneg (sq_nonneg _) (by linarith))
  let A := travel U i.val (route i.val P.center.val 1)
  have hA : G.chord A ≤ r := hr _ _ _
  have hy : q i P.center 1 = G.price (h i * A) := by simp [q,A,Patch.via,hm.1]
  rw [hy] at ht
  have hs := G.chord_price (h i * A)
  have h₁ : 1 ≤ p^2*m := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hp) hO
  have h₂ : 0 ≤ r := (G.chord_nonneg A).trans hA
  have hv : G.chord (h i * A) ≤ (p^2*m)*r := by
    have he : G.chord (h i * A)^2 ≤ (p^2*m)*(r^2) := by linarith
    apply (sq_le_sq₀ (G.chord_nonneg _) (mul_nonneg (by linarith) h₂)).mp
    rw [mul_pow _ r]; exact he.trans (mul_le_mul_of_nonneg_right (le_self_pow₀ h₁ (by decide)) (sq_nonneg r))
  calc
    _ = G.chord (h i * A * A⁻¹) := by simp
    _ ≤ G.chord (h i * A) + G.chord A := by rw [← G.chord_inv A]; exact G.chord_triangle _ _
    _ ≤ (p^2*m)*r + r := add_le_add hv hA
    _ = _ := by unfold p m alignCost; ring

/-- The available chart estimate on the *group* not universal ambient
matrices. -/
def LogReceipt (G : Gauge) (C δ : ℝ) : Prop := 0<C ∧ 0<δ ∧
  ∀ u : G.El, G.chord u ≤ δ → G.lieExp (G.plog (G.mat u)) = u ∧
    ‖G.plog (G.mat u)‖ ≤ C * G.chord u

lemma log_receipt (G : Gauge) : ∃ C δ, LogReceipt G C δ := log_chart_cost G

def ofFrame (h : P.Frame G) : P.FrameCoordinates G :=
  WithLp.toLp 2 (fun i => G.plog (G.mat (h i.1.val)) i.2)

lemma minimizing_writes (hc : LogReceipt G C δ) (hm : P.minimizing U h)
    (hr : ClosePaths P U r) (he : alignCost P*r ≤ δ) :
    P.frameFromCoordinates G (ofFrame P h) = h ∧ ‖ofFrame P h‖ ≤ (points P)*C*alignCost P*r := by
  let v := ofFrame P h
  have hv (i) : readLog P i v = G.plog (G.mat (h i)) := by
    by_cases h : i = P.center
    · subst i; simp only [hm.1,G.mat_one, G.plog_one, read_center]
    ext j
    rw [read_away P h]; rfl
  have hh (i) := hc.2.2 _ ((cluster_root P hm hr i).trans he)
  refine ⟨funext fun i => ?_,?_⟩
  · change P.frameFromCoordinates G v i = _
    rw [frame_read,hv]; exact (hh i).1
  let M := C * (alignCost P*r)
  have hM (i) : ‖readLog P i v‖ ≤ M := by rw [hv]; exact ((hh i).2).trans (mul_le_mul_of_nonneg_left (cluster_root P hm hr i) hc.1.le)
  have hn := (norm_nonneg _).trans (hM P.center)
  have hp := points_ge P
  have ht : ‖v‖ ≤ points P * M := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by linarith) hn)).mp
    rw [frame_counting P v,mul_pow]; apply (Finset.sum_le_sum (g:=fun _ => M^2) (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hM i) _)).trans
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (le_self_pow₀ hp (by decide)) (sq_nonneg _)
  apply ht.trans; unfold M; exact le_of_eq (by ring)

end Compare
end YM.Push.Uniform
