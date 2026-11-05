import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Monitors
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.ParcelBill
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Vault


/-!
# E \eqref{eq:pmult}. The compulsory vertex expense, actual sector

After taking the chart ratio out link for link and keeping the F-fixed
volume reference scalar. Hit can spend all multiplier costs along with
the tree tolerances. Includes every near profile, not conditioned
probabilities; factors on actual stencils with affine subtraction, don't
throw away terms allowing havoc from huge annulus after integration. `Q`
product here is the missing flag prohibitions where not suppressed by
ACTUAL K choices. Charge *pointwise*: permits other masks (q triggers,
broad, etc.) to be used on the same integration marginal, not renewing
this packet grant elsewhere.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Aff
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Mint Laps Wages
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- physical q mask plate (ignored iff suppressed by one of actual
-- chosen incoming addresses' ORIGINAL supports).
def noHolder (R : Activities G f) (L : Finset ℕ) (y : Site f) := y∉ L.biUnion fun i => (R.forced i).support

def edgeBan (R : Activities G f) (L : Finset ℕ) (U : Config G f) (t : ℝ) (i : Site f) : ℝ :=
    if noHolder R L i ∧ i∈ RG.flags t U then 0 else 1

def scenes (m : Stores S) (R : ℕ) := univ.filter fun i => S.ratio.parent i∈m.dome R

def noMore (m : Stores S) (R : Activities G f) (L : Finset ℕ) (Y : Mint T F A x) (a : ArrayR G f) :=
    ∏ i ∈ scenes m (300*radiusB x), edgeBan R L (Y.build a) (fiery G x S.patch.L) i

-- frozen non-tree (including all endpoints tests)
def freeze (F : Forest S.ratio) (p : Stores S) (d : ℕ) := padB p (10*d) \ F.trunks

def pact (m : Stores S) (R : Activities G f) (L : Finset ℕ) (β W : ℝ) (N : ChartRatio G)
    (Y : Mint T F A x) (a : ArrayR G f) :=
    let U := Y.build a
    noMore m R L Y a * curb m Y.V Y.k W x Y.q U * chambers Y m N a *
      Real.exp (-β * coverEnergy Y a m + ∑ i∈ padB m (200*radiusB x),paired Y i -
        Real.log (sLink G N β)*(freeze F m (radiusB x)).card) -- parentheses priority?!

-- verify syntax parse via equality
lemma parses (m : Stores S) (R : Activities G f) (L : Finset ℕ) (β W : ℝ) (N : ChartRatio G) (Y : Mint T F A x)
    (a : ArrayR G f) : pact m R L β W N Y a = noMore m R L Y a * curb m Y.V Y.k W x Y.q (Y.build a) *
    chambers Y m N a * Real.exp (-β*coverEnergy Y a m + (∑ i∈ padB m (200*radiusB x),paired Y i) - Real.log (sLink G N β)*(freeze F m (radiusB x)).card) := by
  rfl

-- prices of products, incl tags only once
lemma tollKit (U : Config G f) (k : S.Choices) (h : S.patch.Branches S.kernel G) :
    (∀ i, |αSite U i k| ≤ (Fintype.card S.patch.FrameTag:ℝ)) ∧
      ∀ i, |αBond U i k| ≤ (Fintype.card S.patch.Points:ℝ) := by
  have hh {v : Type} [Fintype v] (w : v → ℝ) (h : ∀ i,0≤w i) (hv : ∑ i,w i=1) (i : v) :
      |(Fintype.card v:ℝ)*w i| ≤ (Fintype.card v:ℝ) := by
    have he : w i≤1 := hv ▸ single_le_sum (fun i _ => h i) (mem_univ i)
    rw [abs_mul, abs_of_nonneg (by positivity : 0≤(Fintype.card v:ℝ)),abs_of_nonneg (h i)]; exact mul_le_of_le_one_right (by positivity) he -- may gcongr closes
  constructor
  · intro i; let A := expandAt (S.ratio.embed i) U
    apply hh _ _ (S.patch.frameMass_sum h A); intro j; unfold Patch.frameMass; split
    next => positivity
    next => split <;> positivity
  intro i; apply hh _ _ (S.patch.predictorMass_sum (S.connector U k.1 i)) -- args
  intro j; unfold Patch.predictorMass; split
  next => positivity
  next => exact S.patch.weight_nonneg j






end YM.AnalyticNext.ConnectedActivity.Aff
