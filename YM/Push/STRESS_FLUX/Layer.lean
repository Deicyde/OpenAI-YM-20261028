import YM.Push.STRESS_FLUX.Discrete
import YM.Push.STRESS_FLUX.Matching

/-! Smooth sampled version of Discrete.boundaryWeight: unwrap and use
mean values on the two segments. Nonzero nodes are in a compact separated
layer for small mesh, not necessarily *exactly* on gradient support. -/
set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Layer
open Function Set Filter Lattice MeasureTheory Analysis Metric
open scoped Topology BigOperators ContDiff
variable {R : Schedule} {p N : ℕ} {χ : E4 → ℝ} {V : E4 → E4} {a b : Axis} {d : Step} {t : ℝ}

def shift (d : Step) := if d.neg then -(basis d.dir) else basis d.dir
@[simp] lemma shift_norm (d : Step) : ‖shift d‖ = 1 := by unfold shift; split <;> simp
@[simp] lemma shift_rev (d : Step) : shift d.rev = -shift d := by rcases d with ⟨b,_|_⟩ <;> simp [Step.rev,shift]
@[simp] lemma shift_posDir (a : Axis) : shift (posDir a)=basis a := rfl
@[simp] lemma shift_negDir (a : Axis) : shift (negDir a)=-basis a := rfl

lemma place_size {x : Cover} (h : ‖R.gridPoint N x‖ < R.radius p) : R.place (m:=N) (p:=p) (wrap _ x) = R.gridPoint N x := by
  refine congr_arg (R.gridPoint N) (lift_eq_iff.mpr ⟨rfl,fun i => ?_⟩)
  have ht := (PiLp.norm_apply_le (R.gridPoint N x) i).trans_lt h
  rw [Real.norm_eq_abs, abs_lt, Schedule.radius, ← R.span_side N p] at ht
  constructor
  · have hh : (-((R.side N p).val:ℝ)) < 2*x i := by
      apply lt_of_mul_lt_mul_left (a:=R.a N) _ (R.a_pos _).le
      linarith [show -(R.a N * ((R.side N p).val:ℝ) / 2)< R.a N * x i from ht.1]
    exact_mod_cast hh
  have hh : 2*(x i : ℝ) ≤ (R.side N p).val := by
    apply le_of_mul_le_mul_left (a:=R.a N) _ (R.a_pos _)
    linarith [show R.a N * x i < R.a N * ((R.side N p).val:ℝ) / 2 from ht.2]
  exact_mod_cast hh

lemma grid_step (x : Cover) (d : Step) : R.gridPoint N (x + d.vec) = R.gridPoint N x + R.a N • shift d := by
  ext i; rcases d with ⟨b,_|_⟩ <;> by_cases he:i=b <;> simp [Schedule.gridPoint,Step.vec,shift,he,mul_add]
lemma placed_step (x : Site (R.side N p)) (h : ‖R.place x‖ + R.a N < R.radius p) (d : Step) : R.place (x+d.vec) = R.place x + R.a N • shift d := by
  have he : x + d.vec = wrap _ (lift x + d.vec) := by rw [map_add,wrap_lift,wrap_vec]
  rw [he,place_size,grid_step]; rfl
  rw [grid_step]
  apply (norm_add_le ..).trans_lt
  simpa only [norm_smul, Real.norm_of_nonneg (R.a_pos _).le,shift_norm,mul_one,Schedule.place] using h

def half (χ : E4 → ℝ) (t : ℝ) (V : E4 → E4) (z : E4) (d : Step) (b : Axis) :=
    (χ (z+t • shift d)-χ z) / t * V (z+t • shift d) b

def stone (χ : E4 → ℝ) (t : ℝ) (V : E4 → E4) (a b : Axis) (z : E4) :=
    (half χ t V z (posDir a) b - half χ t V z (negDir a) b) / 2

lemma smul_shift (t : ℝ) (d : Step) : ‖t • shift d‖ = |t| := by rw [norm_smul, Real.norm_eq_abs,shift_norm,mul_one]
lemma unwrap (R : Schedule) (hw : HasCompactSupport χ) : ∀ᶠ p : ℕ in atTop, ∀ N : ℕ, ∀ x : Site (R.side N p),
    ∀ (V : E4 → E4) (a b : Axis), Discrete.boundaryWeight (R.a N) (χ ∘ R.place) (V ∘ R.place) x a b = stone χ (R.a N) V a b (R.place x) := by
  obtain ⟨K,hK⟩ := hw.exists_bound_of_continuousOn (continuous_id (X:=E4)).continuousOn
  filter_upwards [R.radius_diverges.eventually (eventually_gt_atTop (K+2))] with p hp N x V a b
  let z := R.place x; let t := R.a N
  have ht : 0<t := R.a_pos N
  have h1 : t ≤ 1 := (R.strictAnti.antitone (Nat.zero_le N)).trans_eq R.a_zero
  have hχ {z : E4} (h : χ z≠0) : ‖z‖ ≤ K := hK z (subset_closure h)
  have h (d : Step) : ((χ ∘ R.place) (x+d.vec) - (χ ∘ R.place) x) / t * ((V ∘ R.place) (x+d.vec)) b = half χ t V z d b := by
    unfold half
    simp only [comp_apply]
    by_cases he : R.place (x+d.vec) = z + t • shift d
    · rw [he]
    have hz : ¬(‖z‖ + t < R.radius p) := mt (fun h => placed_step x h d) he
    have hh : ‖z‖ ≤ ‖z + t • shift d‖ + t := by simpa [smul_shift, abs_of_pos ht] using norm_sub_le (z + t • shift d) (t • shift d)
    have hz' : χ z = 0 := by_contra fun h => hz (by linarith [hχ h])
    have he' : χ (z+t • shift d)=0 := by_contra fun h => hz (by linarith [hχ h])
    have hr : χ (R.place (x+d.vec))=0 := by
      by_contra h; apply he
      have H := placed_step (x+d.vec) (by change _+t<R.radius p; linarith [hχ h]) d.rev
      rw [Step.vec_rev,shift_rev,add_neg_cancel_right,smul_neg,← sub_eq_add_neg] at H
      exact eq_add_of_sub_eq (H.symm)
    simp [z,hr,hz',he'] -- z in he'
  change (2*t)⁻¹ * _ = stone χ t V a b z
  simp only [stone,← h, Step.vec_pos,Step.vec_neg,← sub_eq_add_neg]
  field_simp; ring











end YM.StressFlux.Layer
