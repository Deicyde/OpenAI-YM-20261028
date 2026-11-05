import YM.Org.Theatre
import YM.PhysicalNext.FLAT_PUSH_RESPONSE.OnTrack
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Gaussian
/-!
# Pay on a shifted chart ball before any rescaled limit

Use right-neighborhood (inverse Gaussian *square* scaling), costs here are
entirely V-curvature price fixed-period, no applying theorem as if the
coarse coupling already continued to any new bill. Through derivative 2
only at identity. `Gathered.strict` also chosen before g. zero-dimensional
coordinates included in domain tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.FlatResponse
open Function Filter WilsonStartup.Change Set Metric Asymptotics Next.SectorChange.Gaussian
open scoped Topology BigOperators ContDiff

variable {I : Type} [Fintype I] {F Q : ℝ × Vec I→ℝ}
-- pure scaling, not invoking hats on this integral
abbrev vacWay := 𝓝[>] (0:ℝ)
def high (g : ℝ) := g⁻¹ ^ 2

omit [Fintype I] in
lemma goes_y (y : Vec I) : Tendsto (fun g : ℝ => g • y) vacWay (𝓝 0) := by
  simpa only [zero_smul] using (show Tendsto (fun g : ℝ => g • y) vacWay (𝓝 ((0:ℝ)•y)) from (tendsto_nhdsWithin_of_tendsto_nhds (show Tendsto (fun g : ℝ => g • y) (𝓝 0) _ from (continuous_id.smul continuous_const).tendsto 0)))



structure Gathered (F : ℝ × Vec I→ℝ) (ε r c C : ℝ) : Prop where
  eps_pos : 0<ε
  width_pos : 0<r
  pos : 0<c
  orbit : 0<C
  near : ∀ x∈closedBall (0:ℝ) ε ×ˢ closedBall (0:Vec I) r, ContDiffAt ℝ ω F x
  strict : ∀ y ∈ closedBall (0:Vec I) r, c*‖y‖^2 ≤ F (0,y)
  horizontal₁ : ∀ y∈closedBall (0:Vec I) r, |horizontal F (0,y)| ≤ C*‖y‖^2
  horizontal₂ : ∀ y∈closedBall (0:Vec I) r, |horizontal (horizontal F) (0,y)| ≤ C*‖y‖^2





end YM.PhysicalNext.FlatResponse
