import YM.Push.STATIONARY_UNIFORM.Cost
import YM.Push.STATIONARY_UNIFORM.Switches


/-!
Dressing in a common fine *linear gauge potential* φ (exp φ acts on links
with the inverse on the far endpoint). Allows requesting all forests and
charging even B70 patch operations in the chosen service table. All costs
here (and collar) computed before L given price for φ; no claiming that an
optimal φ for primary valuation has been found. Uniform supplies a local
station path for the real analytic tested-slice problem; should also test
the drift here in any claimed primary use even AFTER re-gauging.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.AtomRegular.Foliage
open Function Set Metric Filter RG Wilson Precision Lattice Tree Pressure Bid Push Uniform Next.Foundations
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical

variable {n m : Side} {k K i j : ℕ} {G : Gauge} {S : StepData m n} {F : Forest S.ratio}

structure Collar (G : Gauge) (k : ℕ) where
  r : ℝ
  count : ℝ
  pos : 0<r
  count_pos : 0<count
  log (x : G.Mat) : x∈closedBall 1 r → Allows k G.plog x count
  group (x : G.El) : G.mat x ∈ closedBall 1 r → G.lieExp (G.plog (G.mat x)) = x

lemma collarSupply (G : Gauge) (k : ℕ) : Nonempty (Collar G k) := by
  obtain ⟨C,δ,hC,hδ,hl⟩ := log_receipt G
  obtain ⟨r,hr,he⟩ := Metric.mem_nhds_iff.mp (G.plog_diff.eventually (by simp))
  let s := min (r/2) (G.colorScale*δ)
  have hi : 0<s := lt_min (half_pos hr) (mul_pos G.colorScale_pos hδ)
  haveI : ProperSpace G.Mat := FiniteDimensional.proper ℝ _
  obtain ⟨Z,hZ,h⟩ := exists_allows (f:=G.plog) (isCompact_closedBall 1 s) (fun i he' => he
    (closedBall_subset_ball (show s < r from lt_of_le_of_lt (min_le_left ..) (half_lt_self hr)) he')) k
  refine ⟨s,Z+1,hi,by positivity,fun i hx => (h i hx).mono (by linarith),fun u hu => (hl u ?_).1⟩
  apply le_of_mul_le_mul_left _ G.colorScale_pos
  rw [Next.Fluctuations.chord_dist u]
  rw [mem_closedBall, dist_eq_norm] at hu; exact hu.trans (min_le_right ..)

abbrev Origin (G : Gauge) (m : Side) := Positions (Primary m G)
abbrev Phi (G : Gauge) (m n : Side) := Origin G m →L[ℝ] (Site n → G.Color)

def vest (φ : Phi G m n) (g : In G m → AxisChart G F) (x : Origin G m) := gauge (fun i => G.lieExp (φ x i)) (Uniform.surface g x)
def plain (φ : Phi G m n) (g : In G m → AxisChart G F) (x : Origin G m) : Directions G n := fun i => G.plog (G.mat (vest φ g x i))

namespace Collar
variable {u t W a : ℝ} {Q : KernelChoices} {A : Before G u t j Q K} {P : Clip} {B : Collar G k}
    {R : PathData G} {φ : Phi G m n} {g : In G m → AxisChart G F} {x : Origin G m}





 -- ≤1














end Collar
end YM.Planned.AtomRegular.Foliage
