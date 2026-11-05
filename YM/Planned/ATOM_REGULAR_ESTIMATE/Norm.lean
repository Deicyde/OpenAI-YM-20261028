import YM.Next.FOUNDATIONS.TestBounds
import YM.Planned.ATOM_REGULAR_ESTIMATE.CrossEffect
import YM.Push.LOCAL_SPLITTING.Calculus


/-! Weight charts for the regular-source input. All estimates are at the given
healthy config (*including equality*). `Directions` uses the finite Pi norm,
not the flavor/Euclidean norm over sites. -/

set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular

open Function Filter Lattice RG Wilson MeasureTheory Push.Local Next.Foundations
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

abbrev Link (n : Side) := Edge (Site n)

def weight (B : BudgetPoint) (o : Site n) (e : Link n) : ℝ :=
  B.threshold * (1+(separation e.1 o:ℝ))^B.power
lemma weight_pos (B : BudgetPoint) (o : Site n) (e : Link n) : 0 < weight B o e :=
  mul_pos B.threshold_pos (pow_pos (by positivity) _)

/-- Linear rescaling by the actually permitted directions. -/
def amp (B : BudgetPoint) (o : Site n) : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi (fun e => (weight B o e) • ContinuousLinearMap.proj e)

@[simp] lemma amp_apply (B : BudgetPoint) (o : Site n) (u : Directions G n) (e : Link n) :
    amp B o u e = weight B o e • u e := rfl

def suppress (B : BudgetPoint) (o : Site n) : Directions G n →L[ℝ] Directions G n :=
  ContinuousLinearMap.pi (fun e => (weight B o e)⁻¹ • ContinuousLinearMap.proj e)

@[simp] lemma suppress_apply (B : BudgetPoint) (o : Site n) (u : Directions G n) (e : Link n) :
    suppress B o u e = (weight B o e)⁻¹ • u e := rfl

@[simp] lemma suppress_amp (B : BudgetPoint) (o : Site n) (u : Directions G n) :
    suppress B o (amp B o u) = u := by
  ext e
  rw [suppress_apply,amp_apply,smul_smul,inv_mul_cancel₀ (weight_pos ..).ne',one_smul]

@[simp] lemma amp_suppress (B : BudgetPoint) (o : Site n) (u : Directions G n) :
    amp B o (suppress B o u) = u := by
  ext e
  rw [amp_apply,suppress_apply,smul_smul,mul_inv_cancel₀ (weight_pos ..).ne',one_smul]

lemma amp_fits (B : BudgetPoint) (o : Site n) {u : Directions G n} :
    B.dirBound o (amp B o u) ↔ ‖u‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num : 0 ≤ (1:ℝ))]
  exact forall_congr' fun i => by
    change ‖amp B o u i‖ ≤ weight B o i ↔ _
    rw [amp_apply,norm_smul_of_nonneg (weight_pos ..).le]
    nth_rw 2 [← mul_one (weight B o i)]
    exact mul_le_mul_iff_right₀ (weight_pos ..)

def charted (F : Config G n → ℂ) (B : BudgetPoint) (o : Site n) (U : Config G n) :=
  (F ∘ increment U) ∘ amp B o

variable {F : Config G n → ℂ} {B : BudgetPoint} {o : Site n} {U : Config G n}

lemma smooth_charted {k : ℕ} (h : Chart k F U) (B : BudgetPoint) (o : Site n) :
    ContDiffAt ℝ k (charted F B o U) 0 :=
  (show ContDiffAt ℝ k (F ∘ increment U) (amp B o 0) by rw [map_zero]; exact h).comp 0 (amp _ _).contDiff.contDiffAt

/-- All input variables may vary at once. At every healthy point. -/
theorem charted_bound {Y : Support n} {k : ℕ} {c : ℝ} (hy : B.Regular Y F) (hp : B.supBounds o Y F c)
    (hU : Healthy B.threshold Y U) (hk : k ≤ B.order) :
    ‖iteratedFDeriv ℝ k (charted F B o U) 0‖ ≤ polarCost k * c := by
  have h : ContDiffAt ℝ k (charted F B o U) 0 :=
    (smooth_charted (k:=B.order) (hy.smooth U hU) B o).of_le (Nat.cast_le.mpr hk)
  refine op_polar (Analysis.sym_Jet h) hp.1 (fun x hx => ?_)
  let v := amp B o x
  have hv : (fun s : ℝ => charted F B o U (s • x)) = fun s : ℝ => F (increment U (s • v)) := by
    ext1 s
    exact congr_arg (F ∘ increment U) (map_smul ..)
  rw [← iteratedDeriv_on_line h x, hv, ← leftDerivs_diag, zero_smul, Work.G07.at_zero_increment]
  exact hp.2 _ hU _ (by simpa using hk) (fun A hA => (List.mem_replicate.mp hA).2 ▸ (amp_fits ..).mpr hx)

end YM.Planned.AtomRegular
