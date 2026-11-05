import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Birthday
import YM.Source.ODE

/-!
# Exact determinant expenses as scalar letters (before placement)

On the actual windows. `local` letters compare those of `A_flat`
with those of `A` (other obligations from locality/entry hypotheses).
Flow marks based on `[0,1]` integral trick, valid even in the nonsymmetric
matrix used in the `C` log. Everything retained at the SAME finite torus.
Here estimates/summability per degree; before turning them into vertices
add footprints, at all path/variant orders, use the other estimates.
Volume multiplies a first sum over all anchors; never pretend this is a
single-root bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Win
open Promise MeasureTheory Filter Matrix ResolventVolume Progress.StationaryScenes
open Green
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {c : Lattice.Side} {n : Type*} [Fintype n] [DecidableEq n] {d : n → Lattice.Site c}

section pays
variable {A : Matrix n n ℝ} {η C : ℝ} (hh : Both d d A η C C) (hη : 0≤η)

include hη hh in
lemma powersBoth (j : ℕ) (hC : 0≤C) : Both d d (A^j) η (C^j) (C^j) := by
  induction j with
  | zero => simpa using identities d η
  | succ j ih => simp only [pow_succ]; exact timesBoth hη ih hh hC (by positivity)

omit [DecidableEq n] in
include hh in
lemma trace_bill : |Matrix.trace A| ≤ (Fintype.card n:ℝ)*C := by
  unfold Matrix.trace
  calc
    _ ≤ ∑ i, |A i i| := Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _ : n,C := Finset.sum_le_sum fun i _ => by simpa [wt] using row_entry hh.1 i i
    _ = _ := by simp

include hη hh in
lemma norm_bill (hC : 0 ≤ C) : ‖A‖ ≤ Fintype.card n * C := by
  have hv i j : ‖A i j‖≤C := by
    simpa only [wt, zero_mul,Real.exp_zero, one_mul, Real.norm_eq_abs] using
      row_entry (monoBoth hh hη le_rfl le_rfl).1 i j
  have ht : (∑ i, ∑ j, ‖A i j‖ ^ 2) ≤ (Fintype.card n * C)^2 := calc
    _ ≤ ∑ _i : n, ∑ _j : n, C^2 := by
      exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv i j) _
    _ = _ := by simp; ring
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two]
  exact (Real.sqrt_le_sqrt ht).trans_eq (Real.sqrt_sq (by positivity))

include hη hh in
/-- Schur, not Frobenius, below one. -/
lemma columns_sum (hC : 0 ≤ C) (ht : C < 1) :
    (1-A).det≠0 ∧ HasSum (fun j : ℕ => A^j) (1-A)⁻¹ := by
  have hs : Summable (fun j : ℕ => A^j) := Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hC ht).mul_left (Fintype.card n:ℝ))
    fun i => norm_bill (d:=d) (powersBoth hh hη i hC) hη (by positivity)
  let X := ∑' j : ℕ,A^j
  have he : X * (1 - A) = 1 := by
    have hv := hs.hasSum.tendsto_sum_nat.mul_const (1-A)
    simp only [geom_sum_mul_neg] at hv
    have hg := (tendsto_const_nhds (x:=1)).sub hs.tendsto_atTop_zero
    rw [sub_zero] at hg
    exact tendsto_nhds_unique hv hg
  constructor
  · have hk : det X * (1-A).det = 1 := by rw [← det_mul,he,det_one]
    exact right_ne_zero_of_mul (hk ▸ one_ne_zero)
  rw [Matrix.inv_eq_left_inv he]; exact hs.hasSum
end pays

section interval


variable (P : Windows n)

/-- Degree-j sum for the determinant of selected precision. Use with
`j=0` for one local bill per x. `J(x) Pi_t` order deliberate (reads the
window of x only in local bill). -/
def ledger (A : Matrix n n ℝ) (j : ℕ) (t : ℝ) := (A-1) * (P.within (flows A t)) *
    ((-P.error (flows A t))^j)

omit [DecidableEq n] in
lemma has_trace {f : ℕ → Matrix n n ℝ} {A} (h : HasSum f A) :
    HasSum (fun i => Matrix.trace (f i)) A.trace := by
  let X := traceAddMonoidHom n ℝ
  exact h.map X (show Continuous (fun a : Matrix n n ℝ => trace a) from continuous_id.matrix_trace)





lemma ledger_price {Y : Promise} {A : Matrix n n ℝ} (hA : Y.Served A d) {B : Turns} (he : B.exp_width ≤ Y.alpha)
    {R : ℕ} (hP : B.Takes P A d R) (i) (t : ℝ) (ht : t∈Set.Icc (0:ℝ) 1) :
    let C := (Y.mass+1)*B.base * B.pace R^i
    Both d d (ledger P A i t) B.exp_width C C := by
  obtain ⟨-,h1,h2,-⟩ := hP.greens t ht
  have hJ := plusBoth hA.2.2.2 (negBoth (identities d Y.alpha))
  rw [← sub_eq_add_neg] at hJ; have hY := Y.mass_pos
  have hs := powersBoth (negBoth h2) B.wide.le i (B.pace_pos R).le
  refine timesBoth B.wide.le (timesBoth B.wide.le (monoBoth hJ he le_rfl le_rfl) h1 B.holds.le (by positivity))
    hs ?_ (mul_nonneg (by positivity) B.holds.le)
  exact pow_nonneg (B.pace_pos R).le _


end interval

section common
variable (P : Windows n) {B : Turns} {A : Matrix n n ℝ} {R : ℕ}












end common
end YM.AnalyticNext.ConnectedActivity.Win
