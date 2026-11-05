import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Weaving

/-!
# Hit for the sector polys

Call with VARIOUS sectors at fixed V, any allowed (indeed dropping some
requirements) incidence, after computing support union from complete
footprints and vast stamp waits. This does not prove output locality
or conflicting-query unchanged. It pays for actual multiplicities over
the actual full products, always uniform per hit across tested V by the
SAME envelope. No shortcuts treating an unrooted volume expenditure as a
per-hit bill. LogIndex vs warnings: `w` may include exponents themselves or
already h. K multiplies. 
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Cash
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Control Window Census Green Mask Pulse
open Coat
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio}
variable {W μ C x : ℝ} {R : YM.ConnectedActivityE6.Target G P} {o : Target.Order G W} {I : Rep G f}
variable (H : Cash W x μ L R o C T I)

/-- book coordinates including dummy Y outside frozen Haar, unintegrated assembly obligations residual -/
def faresP (_H : Cash W x μ L R o C T I) := R.costs L μ I.beta x C
def birth (_H : Cash W x μ L R o C T I) := footprints T I R.halo (radiusB x)
def supportP (i : Head S) := Mixed.foot S R.halo (radiusB x) H.birth i
def unionP (v : Molecule S) := Finset.biUnion v H.supportP

def ticketsP (m r : ℕ) (u : ℝ) (v : Molecule S) := Mixed.Allowed S R.halo (radiusB x) H.faresP
    H.birth (ConnectedActivityE6.lengths T I) m r u v

def shapeW (s : Molecule S) := Mixed.charges S R.halo (radiusB x) H.birth H.faresP
    (ConnectedActivityE6.lengths T I) s

def reward (k : ℕ) (s : Molecule S) := (∏ i∈s,H.text i)*(1+H.shapeW s)^k

def ours (m k r : ℕ) (u : ℝ) (s : Molecule S) := if H.ticketsP m r u s then H.reward k s else 0

lemma attends (s : Molecule S) : H.ticketsP 0 0 0 s ↔ Ac.Spark H.supportP s := by
  have hp : 0≤ H.shapeW s := sum_nonneg fun i _ => add_nonneg (Nat.cast_nonneg _) (show 0≤Mixed.lengths S H.faresP
    (ConnectedActivityE6.lengths T I) i from by rcases i with i|i; exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _); exact Nat.cast_nonneg _)
  exact ⟨fun h=> h.1, fun h => ⟨h,Nat.zero_le _,Nat.zero_le _, hp⟩⟩
lemma charged (m k r : ℕ) (u : ℝ) : Ac.Hit H.unionP (radiusB x) (H.ours m k r u) R.exp (H.faresP.ceiling m k r u) :=
    Mixed.mixed_hit S R.halo (radiusB x) H.faresP H.birth H.opt (ConnectedActivityE6.lengths T I) _ H.laws.acquired H.armed m k r u

lemma price_nn (k : ℕ) (s : Molecule S) : 0 ≤ H.reward k s :=
  Mixed.zero_le_price S R.halo (radiusB x) H.faresP H.birth H.opt (ConnectedActivityE6.lengths T I) _ H.laws.acquired H.armed k s

lemma positive_volume (s : Molecule S) : 0≤H.shapeW s := by
  refine sum_nonneg (fun i _ => add_nonneg (Nat.cast_nonneg _) (show 0≤ Mixed.lengths S H.faresP (ConnectedActivityE6.lengths T I) i from ?_))
  rcases i with i|i
  · exact mul_nonneg H.laws.acquired.extra (Nat.cast_nonneg _)
  exact H.armed.extra _






end Cash

namespace Target
open Filter Function Lattice RG Pressure
open Push Push.AbsoluteSums
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {P : Teller G} (R : YM.ConnectedActivityE6.Target G P)

lemma rate_root (L : Side) {μ β C : ℝ} (h : 0 < μ) : Rate G L R.rate (fun x => (R.costs L μ β x C).rootHit) := by
  let d := μ/16 -- μ/2 *1/2/4
  refine Rate.add ?_ Rate.power
  exact (Rate.monitor_cutoff (show 0<d by unfold d; positivity) (show (0:ℝ)<2 by norm_num)).congr
    (Eventually.of_forall (fun x => by unfold Delay.hatWin; unfold d; simp only [Real.rpow_two]; congr 1; ring))
lemma rate_none (L : Side) {μ : ℝ} (h : 0 < μ) (m k : ℕ) (b : ℝ) : Rate G L R.rate
    (fun x => (R.costs L μ 1 x 0).ceiling m k 0 b) := by
  let c (x) := R.costs L μ 1 x 0
  let q : ℝ := 1/2
  unfold Mixed.Costs.ceiling
  simp only [Nat.cast_zero,mul_zero]
  exact (((rate_root (β:=1) (C:=0) R L h).mul_right (q^m)).mul_right ((1-q)⁻¹)).mul_left (Reserves.extract R.ε k b 0)
end YM.ConnectedActivityE6.Target
