import YM.AnalyticNext.CUBIC_MATCH.Region.Patch

set_option warningAsError false

/-!
# Orienting the frame jets with theirs

Use colors on true matrix frame. Compute second term without normative
loss for many P.Points: apply Hess/focus at fixed G to EACH point,
using self-consistency even at `center`, then apply its stationarity
subtraction to cancel exactly the unknown second orders in the frame
transport. Use noncentral clouds on all routes/points in the patch score with their weight
conventions retained. No symmetry or independence assumptions on the tag!
-/
set_option autoImplicit false
noncomputable section
namespace YM.CubicMatch
open Function Filter Lattice Laurent RG Wilson Precision Exterior Tree Tensor Bid Push Branch
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators
attribute [local instance] Gauge.frobInner

variable {G : Gauge} {μ : Type*} {c f : μ → Side}
  {θ C B : ℝ} {P : Patch} {K : KernelChoices} {V : ∀ p, Dir G (c p) → Dir G (f p)}

section finite
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I]




end finite

/-- matrix nearest. No additional G-chart purchased. -/
def aim (G : Gauge) (x : G.Mat) := G.mat (G.focus x)

private def normF {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (x : E) := ‖fderiv ℝ f x‖
private lemma normF_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → E) (x) : 0≤normF f x := norm_nonneg (fderiv ℝ f x)
def aimSlope (G : Gauge) := normF (aim G) 1
def aimSec (G : Gauge) := ‖sec (aim G) 1‖
lemma aimSlope_nonneg (G : Gauge) : 0≤aimSlope G := normF_nonneg (aim G) 1
lemma aimSec_nonneg (G : Gauge) : 0≤aimSec G := norm_nonneg (sec (aim G) 1)

/-- pre-L. `T` a height for journey. -/
def hatOne (T : ℝ) := 2*T

def cloudOne (T : ℝ) := hatOne T +T

def cloudJetCap (T : ℝ) := hatOne T*T+T^2

def hatTwo (G : Gauge) (T : ℝ) := 2*((aimSec G*cloudOne T*cloudOne T) + aimSlope G*cloudJetCap T)
lemma hatTwo_nonneg (G : Gauge) {T : ℝ} (h : 0≤T) : 0≤hatTwo G T := by
  unfold hatTwo cloudOne cloudJetCap hatOne; have hh := aimSec_nonneg G; have hx := aimSlope_nonneg G; positivity

variable (eqs : ∀ p : μ,(f p).val=(c p).val*P.L.val)
  (t : ∀ p, (perform P K eqs p).SitesChoice)





variable (h : ScaleRead c f P.L (mainRoot eqs) V θ C)
  (he : P.Branches K G)

include eqs t h he



end YM.CubicMatch
