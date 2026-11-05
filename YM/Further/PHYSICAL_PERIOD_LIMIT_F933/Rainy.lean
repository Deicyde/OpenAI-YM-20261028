import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Paintings
import YM.Further.PHYSICAL_PERIOD_LIMIT_F933.Symphony

/-! # Agreement epoch at flat jets (not a claim about amplitudes)

For compatibility checks. We rely on *stationed* equations themselves
with the full map forest. Implicit argument using log-Hessian coords;
no estimates per p needed here. Don't infer global equality of contour
scalar or α/log trajectories living in other choices (see end theorem).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.PhysicalPeriodLimitF933.Rainy
open Gauge Filter Jacobi Macrame Macrame.Lace Polytrace Withdrawal Liquid Enamel Loom Function Lattice RG Tree Matrix Finset Precision Exterior Bid Wilson Set Metric Push.Uniform Push Shingle Pitch Extra.Iteration Extra.Iteration.Calibration
open scoped Topology ContDiff BigOperators Classical
variable {X E F Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

structure Bond (d : ℕ) (f g : X→E) : Prop where
  l : ContDiffAt ℝ ω f 0
  r : ContDiffAt ℝ ω g 0
  rate (j : ℕ) : j≤d → iteratedFDeriv ℝ j f 0=iteratedFDeriv ℝ j g 0
namespace Bond
variable {d n : ℕ} {f g h : X→E}


lemma symm (p : Bond d f g) : Bond d g f := ⟨p.r,p.l,fun j he=>(p.rate j he).symm⟩
lemma trans (p : Bond d f g) (q : Bond d g h) : Bond d f h := ⟨p.l,q.r,fun i he=>(p.rate i he).trans (q.rate i he)⟩


-- combine more general
 -- binder dependent indexes



 -- ht after dsimp A B fails




lemma income (h₁ : ContDiffAt ℝ ω f 0) (h₂ : ContDiffAt ℝ ω g 0) (h : f 0=g 0) (p : ∀ v,Bond d (blade v f) (blade v g)) : Bond (d+1) f g := by
  refine ⟨h₁,h₂,?_⟩; rintro (_|j) hj
  · ext1; simp [h]
  let L (p : X) := ContinuousLinearMap.apply ℝ E p
  ext1 m; rw [iteratedFDeriv_succ_apply_right,iteratedFDeriv_succ_apply_right]
  have he := (p (m (Fin.last j))).rate j (by omega)
  change iteratedFDeriv ℝ j (L (m (Fin.last j)) ∘ fderiv ℝ f) 0=iteratedFDeriv ℝ _ (L (m (Fin.last j)) ∘ fderiv ℝ g) 0 at he
  rw [(L (m (Fin.last j))).iteratedFDeriv_comp_left (h₁.fderiv_right (m:=ω) (by simp)) le_top,(L (m (Fin.last j))).iteratedFDeriv_comp_left (h₂.fderiv_right (m:=ω) (by simp)) le_top] at he
  exact congr_arg (fun (P : ContinuousMultilinearMap ℝ (fun _ : Fin j=>X) E)=>P (Fin.init m)) he

variable {ι : Type} [Fintype ι]



end Bond

section held
variable {d : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
-- purely on entries, even through inverse at Det-positive germs




variable {f g:X→Matrix κ κ ℝ}











end held
end YM.Further.PhysicalPeriodLimitF933.Rainy
