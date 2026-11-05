import YM.Next.EXTRACTION.Tails
import YM.Next.FOUNDATIONS.SU2
import YM.Work.F02.Path

/-!
# Cauchy budgets for left increments on a whole healthy path

Use an analytic-at-zero matrix price in the fixed faithful color normalization,
not the norm of the product identity in a volume-sized matrix. Spend one slice
of the radius per ordered left derivative **within a term**, only through the
fixed order; recenter the whole estimate at each physical step. Hard flags are
never differentiated.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Derivs
open Filter Function Lattice Wilson RG Exterior Precision Work.F02 Metric NormedSpace
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {n : Side}

structure ExpPrice (G : Gauge) where
  r : ℝ
  C : ℝ
  r_pos : 0 < r
  C_pos : 0 < C
  bound (u : G.Mat) : ‖u‖ ≤ r → ‖exp u - 1‖ ≤ C*‖u‖



def update (v : Directions G n) (M : Ambient G n) (z : ℂ) : Ambient G n := fun i =>
    (exp (z • G.colorMat (v i)) * (M i).1, (M i).2 * exp ((-z) • G.colorMat (v i)))





lemma physical_size (U : Config G n) : ‖physical U‖ ≤ ‖(1:G.Mat)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
  have h (x : G.El) := Gauge.mul_frob_eq (G.mat x) (1:G.Mat) (G.mat_star_mul _)
  intro i; change max ‖G.mat (U i)‖ ‖G.mat (U i)⁻¹‖ ≤ _
  simpa! only [Matrix.mul_one] using (show max ‖G.mat (U i) * 1‖ ‖G.mat (U i)⁻¹ * 1‖ ≤ ‖(1:G.Mat)‖ from
    max_le (h _).le (h _).le)

lemma update_bound (P : ExpPrice G) (v : Directions G n) (M : Ambient G n) (z : ℂ) (h : ‖z‖*G.colorScale*‖v‖ ≤ P.r) :
    dist (Derivs.update v M z) M ≤ P.C*(‖z‖*G.colorScale*‖v‖)*‖M‖ := by
  let b := P.C*(‖z‖*G.colorScale*‖v‖)
  have he (u : ℂ) (hu : ‖u‖=‖z‖) (i) : ‖exp (u • G.colorMat (v i)) - 1‖ ≤ b := by
    have ht : ‖u • G.colorMat (v i)‖ ≤ ‖z‖*G.colorScale*‖v‖ := by
      rw [norm_smul, hu, G.colorMat_norm,← mul_assoc]; have := G.colorScale_pos; gcongr; exact norm_le_pi_norm ..
    exact (P.bound _ (ht.trans h)).trans (mul_le_mul_of_nonneg_left ht P.C_pos.le)
  have hb : 0 ≤ b := by unfold b; have := P.C_pos; have := G.colorScale_pos; positivity
  rw [dist_eq_norm]; refine (pi_norm_le_iff_of_nonneg (mul_nonneg hb (norm_nonneg _))).2 fun i => ?_
  change max ‖_*_-_‖ ‖_*_-_‖ ≤ _
  obtain ⟨h1,h2⟩ := max_le_iff.mp (norm_le_pi_norm M i)
  apply max_le
  · rw [← sub_one_mul]; exact (norm_mul_le ..).trans (mul_le_mul (he z rfl _) h1 (norm_nonneg _) hb)
  rw [← mul_sub_one, mul_comm _ ‖M‖]; exact (norm_mul_le ..).trans (mul_le_mul h2 (he (-z) (norm_neg _) _) (norm_nonneg _) (norm_nonneg _))

def rates (f : Ambient G n → ℂ) : List (Directions G n) → Ambient G n → ℂ
  | [] => f
  | v::l => fun M => deriv (fun z : ℂ => rates f l (Derivs.update v M z)) 0





namespace ExpPrice
variable (P : ExpPrice G) (r : ℝ) (d : ℕ)
/-- Slice size in the ambient letter variables for each of up to d left
variations (total room is `r*t`); fee in the complex 1d ray parameter.
Use `fee / directionWeight`; on that circle pay at most one slice. -/
def slice := r/((d:ℝ)+1)
def fee := min (P.r/G.colorScale) (slice r d / (P.C*G.colorScale*(r+‖(1:G.Mat)‖)))
omit P in
lemma slice_pos (hr : 0 < r) : 0 < slice r d := div_pos hr (by positivity)
lemma fee_pos (hr : 0 < r) : 0 < P.fee r d := lt_min (div_pos P.r_pos G.colorScale_pos) (div_pos (slice_pos _ d hr)
    (mul_pos (mul_pos P.C_pos G.colorScale_pos) (add_pos_of_pos_of_nonneg hr (norm_nonneg _))))

lemma next {H t : ℝ} (hr : 0 < r) (hu : 0 < H) (ht : 0 ≤ t) (ht' : t ≤ 1) (v : Directions G n) (U : Config G n) (M : Ambient G n)
    (i : ℕ) (hh : dist M (physical U) ≤ (r-(i+1 : ℕ)*slice r d)*t) (z : ℂ) (hz : ‖z‖ ≤ P.fee r d / H) (hv : ‖v‖ ≤ t*H) :
    dist (Derivs.update v M z) (physical U) ≤ (r-i*slice r d)*t := by
  let e := P.fee r d; let s := slice r d
  have he := P.fee_pos _ d hr
  have hB := slice_pos _ d hr
  have hx : ‖z‖*G.colorScale*‖v‖ ≤ e*G.colorScale*t := calc
    _ ≤ P.fee r d/H*G.colorScale*(t*H) := mul_le_mul (mul_le_mul_of_nonneg_right hz G.colorScale_pos.le) hv (norm_nonneg _) (by have := G.colorScale_pos; positivity)
    _ = _ := by unfold e; field_simp
  have h1 : e*G.colorScale ≤ P.r := (le_div_iff₀ G.colorScale_pos).mp (min_le_left ..)
  have h2 : P.C*(e*G.colorScale)*(r+‖(1:G.Mat)‖) ≤ s := by
    have hv := (le_div_iff₀ (mul_pos (mul_pos P.C_pos G.colorScale_pos) (add_pos_of_pos_of_nonneg hr (norm_nonneg (1:G.Mat))))).mp
      (show e ≤ s/(P.C*G.colorScale*(r+‖(1:G.Mat)‖)) from min_le_right ..)
    linarith
  have h3 := mul_le_of_le_one_right (show 0 ≤ e*G.colorScale from mul_nonneg he.le G.colorScale_pos.le) ht'
  have hy := update_bound P v M z (hx.trans (h3.trans h1))
  have h4 : ‖M‖ ≤ r+‖(1:G.Mat)‖ := by
    have hh' := hh.trans ((mul_le_mul_of_nonneg_right (by simp only [sub_le_self_iff]; positivity : r-(i+1:ℕ)*slice r d ≤ r) ht).trans
      (mul_le_of_le_one_right hr.le ht'))
    rw [dist_eq_norm] at hh'; linarith [norm_sub_norm_le M (physical U),physical_size U]
  refine (dist_triangle _ M _).trans (add_le_add (hy.trans ?_) hh |>.trans (b:=s*t+_) ?_)
  · exact (mul_le_mul (mul_le_mul_of_nonneg_left hx P.C_pos.le) h4 (norm_nonneg _)
      (by have := P.C_pos; have := G.colorScale_pos; dsimp [e]; positivity)).trans (by linarith only [mul_le_mul_of_nonneg_right h2 ht])
  dsimp [s]; push_cast; linarith


end ExpPrice
end YM.Extra.Iteration.Derivs
