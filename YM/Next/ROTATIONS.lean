import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.LinearAlgebra.Multilinear.Pi
import Mathlib.LinearAlgebra.PiTensorProduct.Generators
import YM.Ac.Table
import YM.Next.ROTATIONS.Route
import YM.Org.Theatre
import YM.Pressure.Seeds
import YM.Work.A01
import YM.Work.A02
import YM.Work.A03
import YM.Work.A04
import YM.Work.A05
import YM.Work.A06
import YM.Work.A07
import YM.Work.A08
import YM.Work.A09
import YM.Work.A10
import YM.Work.A11
import YM.Work.A13
import YM.Work.A14
import YM.Work.A15
import YM.Work.A16
import YM.Work.A17

/-!
# B70. Outer spectral estimate and the common rotation descent

Actual missing analytic theorem: `YM.Outer.outer` (just S/J world), hence
`YM.Outer.miles : Bid.Miles`.

See Route and the estimate files below it.

No
producer of UV data (`planet` raw shell laws, `ActLaw`, free MaxwellData, Seed & Grill etc.) claimed here.

A variant/simplification of the strategy
in euclidean-existence, outer-flux/collinear part.

Main choices:

* Work entirely on tested kernels. For true axis-Chamber `V`, time index `i`,
  use `ν V A` from Axis/Word (PVM, undamped, includes atoms). E=p i≥0.
  Weight A is a *finite linear combination*, allowed different words etc.
  Use raw parity including offsets. Axis reflection sign of the lower cluster
  before Laplace; cross fits + slicing + PVM weighted CS (Young) in Axis,
  Slices, Cross. Use ∫ (volume when omitted, Euclidean positions, ℝ for line
  parameters), Probe.hat, keep toll, no trace at time zero. No assumption of
  continuous rotation here.
* Scales and constants in Budget: sequences n, λ=exp(n), fuel x n=λ^x,
  Budget a means eventual bound C fuel a, C≥0. Shape profiles fixed before n.
* Need subpower bound by sign alternation; use transverse moment lemma
  `point_moment` BEFORE choosing band orders: given transverse j≠i & order k
  and axis-pointlike A (`Pressed i A`), t∈(0,1] costs C t⁻ᴰ (mom integrates
  exp(-tE)|p_j|^(2k) in ν V A). True placements for general cluster also
  paid (`placed_moment`). These follow from finite differences.
* Tie interpolation nodes together using fixed ratios in high band. Even
  temporal response for positive E uses 2E/(t²+E²) (t frequency here);
  Mlamp has node factors after subtracting `bake`, cf sunny/lamp_lit, with
  lower bound also at E=0 (`lower`, in Energy). Sign walk on *equal tested
  integrals* on two axes with opposite signs (`alternate`), spending large
  moments to pay high frequency remainders; `Can` induction prices
  bandwidth/order compatibly backwards. `point_cost` for mixed pressed axes,
  `line_cost` including case of non-pressed axis (genuine gap test in Tunnel).
  Main use for cluster on line l, e odd on a,b only; latter estimate for any
  shrink exponents w_j≤0 and q<0, fixed Colors profiles all axes at scales
  fuel(w_j) (L1 scaling). In direction i=l, ∫ in E≤1 of (E+fuel(q))⁻¹ times
  product of transverse profiles, costs Budget δ for any δ>0. When i≠l
  costs Budget (δ−w_l). Includes zero.
* Diagonal stress estimate in `mass`: analogous ∫ in E≤1 of
  E W⁴/(E+W)⁴ times product of transverse profiles (their exponents ≤a),
  W=fuel a (a≤0), in stress ν, costs Budget (4a+δ). Proof:
  - Walk also leads to mixed fixed-band nodal estimates. Use actual derivative
    fields to obtain mixed signs; in odd temporal case compare Lap at residual
    `Tail` (multiply profile by p before baking and divide correction by p).
  - Contact analysis on tensor TESTS (don't need to claim anything about
    density or extension to completed tensor product). Pair Taylor
    subtraction, normalize moment using signed permutations => for frequency
    tests at these small scales with widths ≤W, the contracted momentum
    divergence (source_cost) is O(W³), plus exact contact vanishing on
    moment-controlled tests. Thus tested symbols A,B,C (SelfB R i, BL R i,
    CL R i, respectively, R the normalized Portrait series) obey
    B=p_i² A+O(W⁴), C=p_i² B+O(W⁶), eq without errors after cancellations on
    moment tests (Constraints). No matrix *derivative* positivity needed: use
    the two-band differences testing with annular profiles in i at W and 2W.
    Constrain signs of these three differences using interpolation with the
    same nodes: pay correction terms by fixed-band budgets (constant moments
    in nodal coefficients cancel); on residuals use exact relations and
    resolvent sign flips. `budget_lock` thus limits spectral cost of the gap
    response for A, which by `grant` is enough for the displayed bound.
* Use compact POSITION-supported compensated vector field, then widen the
  target box in spatial frequencies. `chart`: widths λ^(-100) on a,b,
  λ^(-150) on remaining-line-direction (if such), λ^(-300) otherwise.
  `petal a b` uses odd primitive in a, amplitude λ^100. Hence `vane` equals
  the true Killing field locally/eventually, and importantly cross-gradients
  cancel *identically*, leaving only terms supported at exterior gaps. At
  these, no contact corrections; in Thaw treat exterior of low spectral box
  (widened by λ) directly by decay. Cove: shear (`d≠b`) vs diagonal (`d=b`)
  near energy zero; pay mixed with Young vs line & point estimates for shear,
  vs line & diagonal estimate otherwise (split there also at tiny E
  λ^(-3000); for lower, including zero, use large gain from line estimate,
  much cruder estimate okay for stress). Leaves Budget (-1) for exterior
  integrals *including* amplitude. Local parts work by subtracting full Killing
  germs *before* splitting the integrals (uses A01 helpers). Gives angular
  sum zero for all line configurations; translate along line for LineSum.

This file also hooks into all the rest of the A-chain. RGrades remains separate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Outer
open Org Climb Ward Spec Boundary
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius

/-- RSpinJets/RSpinPort/RSpot/RCritical services. Inputs exact contextual
Grades/Diff obligations from the spike. No separate Axis Ward premise. Note
A07 and A13 actually used (inside Town) too; A12 availability independent
(the *input* MaxwellData here already requires marks). -/
theorem commission {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
    (V : DiffPlan S) (W : MaxwellData C) (I : IR (C:=C) S) (H : UV C f S V W I) : Commission V W I H :=
  Bid.station W V I H miles Work.A01.answer Work.A02.answer Work.A03.answer Work.A04.answer
    Work.A05.answer Work.A06.answer Work.A07.answer Work.A08.answer Work.A09.answer
    Work.A10.answer Work.A11.answer Work.A13.answer Work.A14.answer Work.A15.answer
    Work.A16.answer Work.A17.answer


end YM.Outer
