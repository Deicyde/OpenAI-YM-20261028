import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Receipts
import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorWindows
import YM.Extra.ITERATION_NO_LOSS.ComplexDerivs
import YM.Extra.ITERATION_NO_LOSS.Radius
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Clock
import YM.Next.MAXWELL.Caps
import YM.Next.MULTISOURCE.Curves
import YM.Next.UV_STRESS.Currency
import YM.Next.UV_STRESS.Fringe
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.DIRECTED_RECIPE.Economy
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames
import YM.Progress.STATIONARY_SCENES.Green
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.Push.RELAY_MARK.Span
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Pass
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle


/-!
# Conditional Lie jet expenditures in the actual endpoint prescription

One request needs true unmasked position prices through q on every selected
FORWARD gram in use (`Higher`). Not in this file a theorem obtaining those prices
(other than order zero; see AuthorizedLoans now); window, inverse and ordered bounds below are then
conclusions. Rates & bills can depend on patch/step and other fixed post-L
data (and on the witness σ,M for Higher), NEVER on period volume/field/tree
or varying r-window/derivative slots. x also enters the window gain. Use at
any choices licensed here; no extension of a previously issued schedule or
construction of a bake/Directed step. For reconstruction's status (not a
dependency of these jet estimates), see B70FreeDivergence.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Sector
open Lattice Wilson RG Function Filter WardBin.Lies Precision Tree Next.SectorChange
  YM.Pressure Rows Wisps FreeResolvent Affine Mark TestD Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}
  {V : Config G c} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {H : Tube G S} {q : ℕ}
  {σ s M N r d Y g δ Y' : ℝ}

abbrev At (q : ℕ) (a : In (G:=G) x A T → Site c) (d γ : ℝ) := Book (G:=G) (n:=c) (native c) a a Prod.fst q (narrow q d) γ
abbrev cost (q : ℕ) (M Y r u : ℝ) (j : ℕ) := charges j 1 (count q M Y r) (drain u)

structure Loans (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (V : Config G c) (q : ℕ)
    (M d r Y δ g Y' : ℝ) : Prop where
  d_pos : 0 < d
  δ_pos : 0 < δ
  ready : 120 ≤ radiusB x
  exact_inv (u : ℝ) : 0 ≤ u → At q (front A T) d (4*(q+1:ℕ)*d) (fun j => surcharge G j * cost q M Y r u j)
    (exactInv H x A T k u) V
  panes (u : ℝ) : 0 ≤ u → At q (front A T) d (3*(q+1:ℕ)*d) (fun j => surcharge G j * (Y * cost q M Y r u j))
    (rough H x A T k ready u) V
  miss (u : ℝ) : 0 ≤ u → At q (front A T) d d (fun j => surcharge G j * savings q x d M Y r u)
    (rough H x A T k ready u-exactInv H x A T k u) V
  C : At q (front A T) d (3*(q+1:ℕ)*d) (fun j => surcharge G j * (Y*count q M Y r)) (covariance H x A T k) V
  remote : At q (front A T) d d (fun j => surcharge G j * savings q x d M Y r 0) (covariance H x A T k-exactInv H x A T k 0) V
  mismatch : At q (front A T) δ δ (fun j => surcharge G j * haul q x d M Y Y' r g) (kernel H x A T k) V
  gramSlices {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → In (G:=G) x A T) : Injective e → ∀ u : ℝ, 0 ≤ u →
    Book (native c) (front A T ∘ e) (front A T ∘ e) Prod.fst q (narrow q d) (4*(q+1:ℕ)*d)
      (fun j => surcharge G j * cost q M Y r u j) (resolver (fun V => (form H x A T k V).submatrix e e) u) V
  slices {ι : Type} [Fintype ι] [DecidableEq ι] (e : ι → In (G:=G) x A T) : Injective e → ∀ u : ℝ, 0 ≤ u →
    Book (native c) (front A T ∘ e) (front A T ∘ e) Prod.fst q (narrow q δ) (4*(q+1:ℕ)*δ)
      (fun j => surcharge G j * cost q (Y*count q M Y r) Y' g u j) (marginal H x A T k e u) V

lemma loans (p : Price s M r d 1 Y 1 q) (hA : Data (native c) (front A T) Prod.fst q s M r d 1 (form H x A T k) V)
    (hy : (native c).Volume (front (G:=G) (x:=x) A T) d Y) (hR : 120 ≤ radiusB x)
    (hC : FreeResolvent.Gap (covariance H x A T k V) g) (p' : Price d (Y*count q M Y r) g δ 1 Y' 1 q)
    (hy' : (native c).Volume (front (G:=G) (x:=x) A T) δ Y') : Loans H x A T k V q M d r Y δ g Y' := by
  let Z := openings A T G hR
  refine ⟨p.pos,p'.pos,hR,fun u hu => inverse hA p hy hu,fun u hu => window hA p hy hu Z,
    fun u hu => windowDifference hA p hy hu Z (near_survey (boards A T G hR)),?_,?_,?_,fun e he u hu => principal hA p hy hu he,?_⟩
  · exact fromBundle (cloud_bill p hA hy hR) (narrow_nn q p.pos.le) (narrow_use p.pos.le le_rfl) (mul_nonneg p.vol (count_nn p))
  · exact fromBundle (cloud_savings p hA hy hR) (narrow_nn q p.pos.le) (narrow_use p.pos.le le_rfl) (savings_nn p le_rfl)
  · exact fromBundle (residual p hA hy hR hC p' hy') (narrow_nn q p'.pos.le) (narrow_use p'.pos.le le_rfl) (haul_nn p p')
  intro ι _ _ e he u hu; exact principal (cloud_data p hA hy hR hC p') p' hy' hu he

abbrev Query (H : Tube G S) (x : ℝ) (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c) (q : ℕ) (s K r g : ℝ) :=
    let d := TestD.room s K r q
    let Y := key G S.patch d
    let δ := TestD.room d (Y*count q K Y r) g q
    Loans H x A F k V q K d r Y δ g (key G S.patch δ)

lemma pays (hs : 0 < s) (hM : 0 ≤ M) (hr : 0 < r) (hg : 0 < g) (h : Ground H x A T k V s M r g)
    (hσ : 0 < σ) (hF : Higher H x A T k V q σ N) : Query H x A T k V q (min σ s) (max M N) r g := by
  have hA := input hσ hs hM hr h hF
  have p := plan (q:=q) (lt_min hσ hs) (hM.trans (le_max_left M N)) hr S.patch G
  have p' := plan (q:=q) p.pos (mul_nonneg p.vol (count_nn p)) hg S.patch G
  exact loans p hA (keys _ _ _ p.pos) h.ready h.cloud_gap p' (keys _ _ _ p'.pos)

/-- Post-L, ordered and ordinary derivative roles kept separate. The only
additional jet input for the request is on the FORWARD Gram. Ground
constants/gaps bought even before request. The extra receipts `key`, `room`
etc at two precisions have explicit post-L dependence (also on the request,
e.g. σ,N) and use no jets of inverses as inputs. All evaluated at the real
V with the same selected shot set/tree/correct output flags and with *true*
Lie derivatives, including of window discrepancy to shift-resolvent and of
C itself as used at `cloud C`. Delayed, doesn't already yield prices under
an arbitrary Wait or even a single Teller.Funds. No local logarithm or
likelihood estimate on wrong-flag stencils. Does not assume other modules'
higher selected-precision estimates have been verified; can consume `Higher`
if they are later built. -/
theorem commissioned (G : Gauge) (P : Patch) (Pt : Teller G) (hp : P.Branches Pt.bind G) :
    ∃ s M r g : ℝ, 0 < s ∧ 0 ≤ M ∧ 0 < r ∧ 0 < g ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (H : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S H →
    ∀ (A : Stores S) (F : Forest S.ratio) (k:S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
    Ground H x A F k V s M r g ∧ ∀ q σ N, 0 < σ → Higher H x A F k V q σ N → Query H x A F k V q (min σ s) (max M N) r g := by
  obtain ⟨s,M,r,g,hs,hM,hr,hg,h⟩ := ground_supply G P Pt hp
  refine ⟨s,M,r,g,hs,hM,hr,hg,h.mono fun x hx c f S H hS hR hT A F k V hV => ?_⟩
  have h0 := hx S H hS hR hT A F k V hV
  exact ⟨h0,fun q σ N => pays hs hM hr hg h0⟩
end YM.SelectedOrderedKernels.Sector
