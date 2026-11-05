import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Currency
import YM.Next.EXTRACTION.Relay
import YM.Progress.STATIONARY_SCENES.Green
import YM.Progress.STATIONARY_SCENES.Response


/-!
# Weight meters for the mixed estimates
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Estimate
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson
open Progress.StationaryScenes YM.Next.Free
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators

variable {G : Gauge}

section step
variable {n l : Side} {ι : Type*} {η : ℝ} {P : Purse ι (Site n)}

def tollRate (P : Purse ι (Site n)) (l : Side) (η : ℝ) := ∀ i x y,
    P.toll i x ≤ Green.wt (η / l.val) x y * P.toll i y

def guide (l : Side) (η : ℝ) (r : ℕ) := Real.exp (η/l.val*r)
lemma guide_pos (l : Side) (η : ℝ) (r : ℕ) : 0 < guide l η r := Real.exp_pos _

lemma enters (h : tollRate P l η) (he : 0 ≤ η) (i : ι) (x y : Site n) (r : ℕ) (hr : separation x y ≤ r) :
    P.toll i x ≤ guide l η r* P.toll i y := by
  apply (h ..).trans (mul_le_mul_of_nonneg_right (Real.exp_monotone ?_) (P.toll_pos ..).le)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hr) (div_nonneg he (by positivity))
lemma guide_le (l : Side) (r : ℕ) (η : ℝ) (he : 0 ≤ η) : guide l η r ≤ Real.exp (η*r) := by
  apply Real.exp_monotone; exact mul_le_mul_of_nonneg_right (div_le_self he (by exact_mod_cast l.property)) (by positivity)
lemma advancing (w : Walk) (x : Site n) : separation x (stop x w) ≤ w.length := by
  induction w generalizing x with
  | nil => simp [stop]
  | cons a w ih => rw [stop]; exact ((separation_triangle ..).trans (Nat.add_le_add (Response.by_one x a).1 (ih _))).trans_eq (show 1+w.length=(a::w).length from by simp [add_comm])
lemma shifting (P : Purse ι (Site n)) {X : Type*} [NormedAddCommGroup X] {f : Site n → X} {S : Finset ι} (h : tollRate P l η) (he : 0 ≤ η)
    {C : ℝ} (hf : P.Pays S f C) (r : ℕ) (t : Equiv.Perm (Site n)) (ht : ∀ x, separation x (t x) ≤ r) :
    P.Pays S (f ∘ t) (guide l η r ^ S.card*C) := by
  apply Purse.Pays.relocate t hf (pow_nonneg (guide_pos ..).le _)
  intro i; rw [← mul_assoc];
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  apply (Finset.prod_le_prod (fun _ _ => (P.toll_pos ..).le) (fun j _ => enters h he j i _ _ (ht i))).trans_eq; simp [Purse.price,Finset.prod_mul_distrib]

lemma succ_guide (l : Side) (r : ℕ) (η : ℝ) : guide l η (r+1)=guide l η r*guide l η 1 := by
  unfold guide; rw [← Real.exp_add]; push_cast; ring_nf
end step

end YM.AnalyticNext.QuarticMatch.Estimate
