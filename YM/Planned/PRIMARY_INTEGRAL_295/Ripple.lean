import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Calculus.VectorField
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Analysis.Polydisc
import YM.Bid.Fuels
import YM.Work.A05.Read
import YM.Work.A07


/-!
# Local real marginal integrals, continuous k-jet germs at protected calls

Input may vary with path (chosen chart over a neighborhood of actual
V INCLUDING equality call), keeps ρ and joint μ the same throughout.
No sup of derivative of indicators; map is pre-mask, smooth, comparison
with masked pointwise uses Raw. Here only analytic permission to differentiate
for customer, deliberately no uniform domination across charts.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Ripple
open Function Filter Set Metric MeasureTheory
open scoped Topology ContDiff BigOperators
variable {E F Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
variable [MeasurableSpace Ω] {M : Measure Ω}
variable {X : Ω→E→F} {S : Set E} {n k : ℕ}

def value (X : Ω→E→F) (M : Measure Ω) (x : E) := ∫ z:Ω,X z x ∂M

def report (X : Ω→E→F) (n : ℕ) (x : E) (z : Ω) := iteratedFDeriv ℝ n (X z) x

def bubble (X : Ω→E→F) (M : Measure Ω) (n : ℕ) (x : E) := ∫ z:Ω, report X n x z ∂M

structure Supper (X : Ω→E→F) (M : Measure Ω) (k : ℕ) (S : Set E) : Prop where
  room : IsOpen S
  contour : ∀ᵐ z ∂M, ∀ x∈S, ContDiffAt ℝ k (X z) x
  ordinary : ∀ n ≤ k, ∀ x∈S, AEStronglyMeasurable (report X n x) M
  volume : ∀ n ≤ k, ∃ b:Ω→ℝ, Integrable b M ∧ ∀ᵐ z ∂M, ∀ x∈S, ‖report X n x z‖ ≤ b z

namespace Supper
lemma serves (h : Supper X M k S) {x : E} (hx : x∈S) (hn : n≤k) : Integrable (report X n x) M := by
  obtain ⟨b,hb,hc⟩:=h.volume n hn; exact hb.mono' (h.ordinary n hn x hx) (hc.mono fun a ha=> ha x hx)


lemma pearl (h : Supper X M k S) {x : E} (hx : x∈S) (hn : n≤k) : ContinuousAt (bubble X M n) x := by
  obtain ⟨b,hb,hc⟩:=h.volume n hn
  apply tendsto_integral_filter_of_dominated_convergence b _ _ hb
  · filter_upwards [h.contour] with z hz; exact ((hz x hx).continuousAt_iteratedFDeriv (Nat.cast_le.mpr hn)).tendsto
  · filter_upwards [h.room.mem_nhds hx] with y hy; exact h.ordinary n hn y hy
  filter_upwards [h.room.mem_nhds hx] with y hy; exact hc.mono fun _ hz=> hz y hy

private def turner (n : ℕ) (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Tensor.T E F (n+1) ≃L[ℝ] (E→L[ℝ] Tensor.T E F n) := (continuousMultilinearCurryLeftEquiv ℝ _ _).toContinuousLinearEquiv
private lemma turn_norm (z : Tensor.T E F (n+1)) : ‖turner n E F z‖=‖z‖ := (continuousMultilinearCurryLeftEquiv ℝ (fun _=>E) F).norm_map _

private lemma spring_at (h : Supper X M k S) {x : E} (hx : x∈S) (hn : n<k) :
    HasFDerivAt (bubble X M n) ((turner n E F) (bubble X M (n+1) x)) x := by
  obtain ⟨b,hb,hc⟩:= h.volume (n+1) hn
  let A:=turner n E F
  let G (x : E) (z : Ω) := A (report X (n+1) x z)
  have he : HasFDerivAt (bubble X M n) (∫ z, G x z ∂M) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (F:=report X n) (F':=G) (h.room.mem_nhds hx) _
      (h.serves hx hn.le) _ _ hb
    · filter_upwards [h.contour] with z hz; intro y hy
      have hd := (hz y hy).differentiableAt_iteratedFDeriv (Nat.cast_lt.mpr hn)
      have hp : G y z=fderiv ℝ (iteratedFDeriv ℝ n (X z)) y := by
        unfold G report A; rw [iteratedFDeriv_succ_eq_comp_left]; exact (turner n E F).apply_symm_apply _
      rw [hp]; exact hd.hasFDerivAt
    · filter_upwards [h.room.mem_nhds hx] with y hy; exact h.ordinary n hn.le y hy
    · exact A.continuous.comp_aestronglyMeasurable (h.ordinary (n+1) hn _ hx)
    filter_upwards [hc] with z hz; intro y hy; unfold G A; rw [turn_norm]; exact hz _ hy
  have HH : (∫ z:Ω,G x z ∂M)=A (bubble X M (n+1) x) := by
    exact @ContinuousLinearEquiv.integral_comp_comm Ω (Tensor.T E F (n+1)) (E→L[ℝ] Tensor.T E F n) _ M ℝ _ _ _ _ _ _ _ A _
  rw [HH] at he; exact he

lemma stirring (h : Supper X M k S) {x : E} (hx : x∈S) (hn : n≤k) : iteratedFDeriv ℝ n (value X M) x=bubble X M n x := by
  induction n generalizing x with
  | zero =>
    unfold value bubble report; simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply];
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ n ih =>
    have hh : iteratedFDeriv ℝ n (value X M) =ᶠ[𝓝 x] bubble X M n := by
      filter_upwards [h.room.mem_nhds hx] with y hy; exact ih hy (by omega)
    have hp := (spring_at h hx hn).congr_of_eventuallyEq hh
    apply (turner n E F).injective
    rw [iteratedFDeriv_succ_eq_comp_left]; exact ((turner n E F).apply_symm_apply _).trans hp.fderiv

lemma flare (h : Supper X M k S) (x : E) (hx : x∈S) : ContDiffAt ℝ k (value X M) x := by
  have ht (n : ℕ) (hn:n≤k) {x:E} (hx:x∈S) : iteratedFDerivWithin ℝ n (value X M) S =ᶠ[𝓝 x] bubble X M n := by
    filter_upwards [h.room.mem_nhds hx] with x hx; rw [iteratedFDerivWithin_of_isOpen _ h.room hx, stirring h hx hn]
  apply ContDiffOn.contDiffAt _ (h.room.mem_nhds hx)
  apply (contDiffOn_nat_iff_continuousOn_differentiableOn h.room.uniqueDiffOn).mpr
  refine ⟨fun n hn x hx=> ?_, fun n hn x hx=>?_⟩
  · exact ((pearl h hx hn).congr_of_eventuallyEq (ht n hn hx)).continuousWithinAt
  exact ((spring_at h hx hn).congr_of_eventuallyEq (ht n hn.le hx)).differentiableAt.differentiableWithinAt
end Supper

def Regales (X : Ω→E→F) (M : Measure Ω) (k : ℕ) (x : E) : Prop := ∃ S:Set E, x∈S ∧ Supper X M k S
end YM.Planned.PrimaryIntegral295.Ripple
