import YM.Next.EXTRACTION.Relay
import YM.Next.FREE_KERNELS.Curl
import YM.Next.SCHEDULE.GridCost
import YM.Planned.STATIONARY_JET_PORT.InUse

set_option warningAsError false
/-!
# Measure and inherited path terms for existing thermal interface

Actual product over the FREE links at the same stationary solution, no
replacement of the ChartRatio (Haar and chart normalization tied by the
supplied LocalRatio). `warm` gives the open radius; pays compact derivative
cost in Color *before* L. For `Precision.loop` also read EVERY existing Atom
term via true length prices; in particular doesn't discard the inherited
correction when controlling all finite-order external jets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.JetPort
open Push Push.Uniform Filter Function Set Metric Lattice Matrix RG Precision Tree Bid
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius InnerProductSpace
variable {G : Gauge} {c f : Side} {S : StepData c f} {B : Forest S.ratio}
    {p : Clip} {R : PathData G} {Q : KernelChoices} {μ C Λ : ℝ} {N j : ℕ}
    {A : Before G μ C j Q (N+3)}
    {g : In G c → AxisChart G B}



def pigment (G : Gauge) (B : Forest S.ratio) (i : B.Free) : Positions (Key B G) →L[ℝ] G.Color :=
  (ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _ => G.Color) i).comp ((tint G _).toContinuousLinearMap)


-- local pre-L purchase
structure FiberFee (O : ChartRatio G) (k : ℕ) where
  cost : ℝ
  positive : 0<cost
  invoice : ∀ z∈closedBall 0 (O.radius/2), Allows k (fun z => Real.log (O.J z)) z cost

lemma purchase (O : ChartRatio G) (hO : LocalRatio O) (k : ℕ) : Nonempty (FiberFee O k) := by
  obtain ⟨P,h,H⟩ := exists_allows (f:=fun z => Real.log (O.J z)) (isCompact_closedBall 0 (O.radius/2))
    (fun x hx => by
      have ht := closedBall_subset_ball (half_lt_self hO.patch) hx
      exact (hO.germ x ht).log (hO.pos x ht).ne') k
  exact ⟨1+P,by positivity, fun x hx => (H x hx).mono (le_add_of_nonneg_left zero_le_one)⟩

-- Compact Haar price needs room. Buy exactly this thermal radius (per
-- estimator; common g across estimators below). Always within accepted
-- Uniform Before.Service.heatLimit, and prove for actual path point.
open Before.Service

def warm (O : ChartRatio G) (Y : ChartPrices) (N : ℕ) :=
  min Y.horizon (O.radius/(2*shade G*trailCost Y (N+3)))

variable {O : ChartRatio G} {D : FiberFee O (N+1)}

def warmth (O : ChartRatio G) (Y : ChartPrices) (N : ℕ) := O.radius/2+shade G*pathCost Y (N+1)
def tax (O : ChartRatio G) (fee : ℝ) (Y : ChartPrices) (N : ℕ) :=
  partitionsBill (N+1)*(fee*(1+warmth O Y N)^(N+1)) * ((Fintype.card Axis:ℝ)) *
    countCost (pathRate Y N/2)
def taxRate (Y : ChartPrices) (N : ℕ) := weaker (N+1) (pathRate Y N)

section Real
variable (hg : A.Service B p R g) (hp : R.Bounds p μ C Λ) (hK : Larger (G:=G) S) (hj : S.patch.J=j) (ht : S.kernel=Q) (hO : LocalRatio O)
include hg hp hK hj ht hO
local notation "Y" => A.tables p S.patch
local notation "dim" => S.Choices
local notation "Inx" => (Positions (Primary c G))



omit hO in
lemma calorimeter {x : Inx} (hx : x ∈ ball 0 (warm O Y N)) (i : B.Free) :
    g (tint G _ x) i ∈ ball 0 (O.radius/2) := by
  let Z := Uniform.station g
  let T := trailCost Y (N+3)
  obtain ⟨hu,H⟩ := hg.trail_lipschitz hp hK hj ht
  have he := H x (ball_subset_ball (min_le_left ..) hx) 0 (Metric.mem_ball_self hg.x_pos)
  change ‖Z x-Z 0‖ ≤ T * ‖x-0‖ at he
  have h₀ : Z 0 = 0 := by unfold Z Uniform.station; simp [hg.critical.1]
  rw [h₀,sub_zero,sub_zero] at he
  rw [mem_ball_zero_iff]; apply lt_of_le_of_lt (norm_le_pi_norm _ i)
  have hS := shade_pos G
  calc
    ‖g (tint G _ x)‖ ≤ shade G * ‖Z x‖ := by simpa [Z,Uniform.station] using tint_le (Z x)
    _ ≤ shade G * (T*‖x‖) := mul_le_mul_of_nonneg_left he hS.le
    _ < _ := by
      have hv : ‖x‖ < warm O Y N := by simpa using hx
      have hh := (lt_div_iff₀ (mul_pos (mul_pos (by norm_num : (0:ℝ)<2) hS) hu)).mp (hv.trans_le (min_le_right ..))
      unfold T; linarith only [hh]


end Real
end YM.Planned.JetPort
