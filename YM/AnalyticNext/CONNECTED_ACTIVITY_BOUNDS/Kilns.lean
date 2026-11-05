import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Bearer
import YM.AnalyticNext.CONNECTED_ACTIVITY_BOUNDS.Halls

/-!
# Packing formula and budgets

Exact candidate dictionary of values on this step. F a parameter
(e.g. use ANY forest; not proving yet existence for successive steps),
not re-chosen from factor to factor. One reference with inactive Gaussians
and dummy free Haar of mass 1. `payfield` defines term USING actual frozen
variables and actual output flag table extended only off-component. Bond and
frame tags with PRE-eligibility UNIFORM priors. All coupling-dependent
volume multipliers INCLUDED except common ($β,T,F$, extensive etc) charged
outside word-level expansion. Need proof of ancestry, support accounting
for variation between components, etc to deploy in exact integral.

`Preceded` local criteria in addition to which each numerical letter
has authentic eligibility (may just be zero then). Does not proliferate
K multiplicities/witness variants even when a letter pays a K. budget marks
for summations can remove occurrences even if alters representation; don't
interpret derivative prices as extending the evaluation across masks!
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.ConnectedActivity.Cab
open Filter Function Lattice RG Precision Wilson Pressure Pressure.Stores Exterior Bloch Turn MeasureTheory
open Matrix Work.F03 Progress.StationaryScenes Push.SectorMeasure Push.SectorMeasure.Oriented
open Push.AbsoluteSums Tree Next.Fluctuations Finset Win Win.Promise Green Rates Aff Aff.Mint Laps Wages
open Centered Centered.Till Jewels Footprint Paths Chains Calls Mixed
open scoped Topology BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
variable {G : Gauge} {c f n : Side} {S : StepData c f} {T : Tube G S} {x : ℝ} {F : Forest S.ratio} {A : Stores S}

-- exact record table assignment criteria. Doesn't demand off-support
-- flags have no effect on JOIN in A* (query larger than support if tested);
-- pay standalone using only own halos with augmentation.
def panes (S : StepData c f) (s : Finset (Tab S)) : Finset (Stores S) := s.toLeft
def holds (S : StepData c f) (s : Finset (Tab S)) : Finset ℕ := s.toRight.toLeft

def storeAt (S : StepData c f) (s : Finset (Tab S)) := Packets.store S ((panes S s).biUnion (Packets.seeds S))

def restore (S : StepData c f) (s : Finset (Tab S)) (x : ℝ) (V : Config G c) : Stores S := { storeAt S s with flags := RG.flags (temp x) V }

def surface (S : StepData c f) (T : Tube G S) (R : Rep G f) (x : ℝ) (s : Finset (Tab S)) :=
    s.biUnion (reach T x R)

def Mandatory (S : StepData c f) (x : ℝ) (s : Finset (Tab S)) :=
    (∀ p∈panes S s, Packets.connected S 500 (radiusB x) p) ∧
      (↑(panes S s): Set (Stores S)).Pairwise fun i j => Disjoint (i.dome (500*radiusB x)) (j.dome (500*radiusB x))

def meetsFlag (S : StepData c f) (R : Rep G f) (i : ℕ) (A : Stores S) :=
    ∀ x ∈ (R.activities.forced i).inventory,∃ j∈ A.costs,x∈RG.touched j

def Overs (R : Rep G f) (B : Finset ℕ) := (↑B:Set ℕ).Pairwise fun i j => Disjoint (R.activities.forced i).support
      (R.activities.forced j).support

structure Preceded (T : Tube G S) (R : Rep G f) (x : ℝ) (s : Finset (Tab S)) (V : Config G c) : Prop where
  coherent : Mandatory S x s
  output : (storeAt S s).flags=RG.flags (temp x) V ∩ surface S T R x s
  tilts : Overs R (holds S s)
  forced i : i∈holds S s → meetsFlag S R i (storeAt S s)
  aligned i : i∈ panes S s → Installed i (restore S s x V) (450*radiusB x)
  links : Ac.Spark (reach T x R) s

-- active-col covariance independent even of `q,H.Mints`
def coRef (T : Tube G S) (x : ℝ) (V : Config G c) (F : Forest S.ratio) (A : Stores S) :=
    (eyes S G (radiusB x)).cov (gram T F x A V)

def demand (T : Tube G S) (x : ℝ) (V : Config G c) (F : Forest S.ratio) (A : Stores S) :=
    Centered.law (coRef T x V F A)⁻¹

lemma normalized_law (t : Promise.Turns) (T : Tube G S) (x : ℝ) (V : Config G c) (F : Forest S.ratio) (A : Stores S)
    (ht : t.Takes (eyes S G (radiusB x)) (gram T F x A V) (dcol S) (paceR x)) :
    let S' := coRef T x V F A
    S'.PosDef ∧ (takePaid t).Safe S'⁻¹ ∧ IsProbabilityMeasure (demand T x V F A) := by
  intro M
  have he : PosDef M := Centered.symmetric_bottom t.feet ht.precision.1 (Windows.cov_hermitian ..)
  refine ⟨he,⟨he.inv.isHermitian, ?_⟩, probability he.inv⟩
  simpa only [takePaid, add_halves] using! ht.precision.2

def figure (T : Tube G S) (x r : ℝ) (h : Chi) (A : Stores S) (F : Forest S.ratio) (V : Config G c)
    (k : S.Choices) (y : F.Slice G) : Mint T F A x := ⟨V,y,h,k,r,holdSize G S.patch x⟩

def payfield (T : Tube G S) (x r W : ℝ) (R : Rep G f) (N : ChartRatio G) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (k : S.Choices) (h : Chi) (s : Finset (Tab S)) (L : Finset ℕ) (y : F.Slice G) (z : ArrayR G f) :=
    ∏ i ∈ s, leaf T x W R N L (figure T x r h A F V k y) z i

def juice (T : Tube G S) (x W r : ℝ) (R : Rep G f) (N : ChartRatio G) (A : Stores S) (F : Forest S.ratio)
    (V : Config G c) (h : Chi) (s : Finset (Tab S)) (L : Finset ℕ) (k : S.Choices) :=
    ∫ y, ∫ z, payfield T x r W R N A F V k h s L y z ∂demand T x V F A ∂F.order G

/-- Physical choice expectation conditional on frozen and common window. Valid even with off-tag bound equality
burning retained walks. For M.Criterion no extra order due to repeated binder. -/
def extraction (T : Tube G S) (x W r : ℝ) (N : ChartRatio G) (R : Rep G f) (F : Forest S.ratio) (V : Config G c)
    (h : Chi) (s : Finset (Tab S)) (L : Finset ℕ) (A : Stores S) :=
    (Fintype.card S.Choices : ℝ)⁻¹ * ∑ k, juice T x W r R N A F V h s L k

def centre (T : Tube G S) (x W r : ℝ) (N : ChartRatio G) (R : Rep G f)
    (F : Forest S.ratio) (h : Chi) (s : Finset (Tab S)) (V : Config G c) :=
    if Preceded T R x s V then extraction T x W r N R F V h s (holds S s) (restore S s x V) else 0

section fires
-- Note normalization order and ENVELOPES. Assuming inputs obtained from Book,
-- not as postulated existence of monadic partition.
variable (T : Tube G S) (F : Forest S.ratio) (x W r : ℝ) (R : Rep G f) (N : ChartRatio G)


end fires
end YM.AnalyticNext.ConnectedActivity.Cab
