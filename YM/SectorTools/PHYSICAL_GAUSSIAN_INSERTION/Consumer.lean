import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Agreements
import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Bias
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Extra.ITERATION_NO_LOSS.Kernels
import YM.Extra.ITERATION_NO_LOSS.Rebuild
import YM.Extra.MULTISOURCE_BOUNDS.Inheritance
import YM.Extra.MULTISOURCE_TRAJECTORIES.Adjoint
import YM.Extra.MULTISOURCE_TRAJECTORIES.Deletion
import YM.Extra.MULTISOURCE_TRAJECTORIES.Price
import YM.Extra.SOURCE_HISTORIES.Accompany
import YM.Extra.WEAK_SCALING_ACTLAW.Divergence
import YM.Extra.WEAK_SCALING_ACTLAW.Five
import YM.Extra.WILSON_STARTUP.Clock
import YM.Extra.WILSON_STARTUP.Overlay
import YM.Next.MAXWELL.Kernel
import YM.Next.MULTISOURCE.Curves
import YM.Next.WARD_BIN.LabelEst
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.Progress.JOINT_CALENDAR.Issue
import YM.Progress.STATIONARY_SCENES.Frames
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Reconstruct
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Models
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Passage
import YM.Push.ABSOLUTE_SUMS.Mixed
import YM.Push.CORRECTED_COLUMNS.Assembly
import YM.Push.CORRECTED_COLUMNS.Calibration
import YM.Push.CORRECTED_COLUMNS.Funding
import YM.Push.FINITE_DETECTION.Crew
import YM.Push.GRID_APPROXIMATION.AttachDefs
import YM.Push.GRID_APPROXIMATION.Estimate
import YM.Push.GRID_APPROXIMATION.Polynomial
import YM.Push.LOCAL_SPLITTING.Clocks
import YM.Push.RELAY_DIFFERENCE.Rolling
import YM.Push.RELAY_MARK.Linear
import YM.Push.STATIONARY_UNIFORM.Paths
import YM.Push.STRESS_FLUX.Haar
import YM.Push.STRESS_FLUX.Low
import YM.Push.STRESS_FLUX.Matching
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Canonical
import YM.SectorNext.VACUUM_NORMALIZATION.Bulk
import YM.SectorTools.PHYSICAL_GAUSSIAN_INSERTION.Insertion
import YM.UVNext.COMMON_GRADE_ASSEMBLY.Free
import YM.UVNext.COUPLING_RESET.Prices
import YM.UVNext.COUPLING_RESET.Reset
import YM.UVNext.FREE_STRESS_CERTIFICATE.Triangle



/-!
# Gaussian Lp consumer: a piece of the actual Frco correction

Conditional Z calculation. A set of true regular positive bond/color slots
on the *selected* sector (Lean endpoint prescription `fog`). Insert the
quadratic and affine charges of `adjustment` *on these slots*, as a localized
perturbation of the exact Gaussian under the change. No changing the
covariance at every use, erasing the rest of `adjustment` from the physics,
or trading a Gibbs expectation here.

Local in Z **only**. The exponent coefficients can use ALL the supplied data
(paths, branches, tags, license choices, Held Y etc.). For instance NO claim
this insertion reads only these sites in V; in polymer applications further
support and cost analysis is needed even to use the entries as letters. An
arbitrary support is allowed, so the theorem can give an extensive bound if
that support is extensive.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SectorTools.PhysicalGaussianInsertion.Physical

open MeasureTheory Function Filter Set Matrix
open Lattice RG Pressure Wilson Pressure.Tube Pressure.Stores Tree Precision
open AnalyticBridge.Covariance
open AnalyticBridge.GaussianFieldAlignment (Ready)
open Next.SectorChange Next.SectorChange.Gaussian Next.SectorChange.Wisps Push.SectorMeasure
open scoped Topology ContDiff BigOperators Classical ENNReal Matrix.Norms.Frobenius

variable {G : Gauge} {c f : Side} {S : StepData c f}

/-- Keep actual chart shift from the ORDERED Gaussian data (including actual
Held variables and V); restrict a part of the exponent that depends on z.
Locality in z only. Note original constant still belongs to the remaining
price, not a claim amounts of those other factors are negligible. -/
def piece (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (H : Stores S) (F : Forest S.ratio)
    (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen H x F)) (g : ℝ)
    (P : Finset (Rows.In x H F (G:=G))) (z : Prices G (Active H x F)) :=
  let m := meanLog H F T x V k q d Y
  let B := Rows.adjustment T x V k (shots S x) H F q d Y (fog H F T x V k) m g
  B (maskVec P z) - B 0

def book (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (H : Stores S) (F : Forest S.ratio)
    (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen H x F)) (g : ℝ)
    (P : Finset (Rows.In x H F (G:=G))) (p cost : ℝ) :=
  let C := fog H F T x V k
  let m := meanLog H F T x V k q d Y
  let Q := Rows.gram T x V k (shots S x) H F
  let t := Rows.eta T x V k (shots S x) H F q d Y m g
  let A := (C⁻¹ - maskForm P (C⁻¹-Q))⁻¹
  Inserted P C A (A *ᵥ maskVec P t) p cost (piece T x V k H F q d Y g P)

/-- Relative linear exponent price. `B` from the path/source bound,
not the number of sites. Coupling inverse and chart radius stay until
priced. -/
def load (x g d M B s : ℝ) :=
  g⁻¹ * ((M*(M * Real.exp (-s * ((radiusB x/60:ℕ):ℝ)))) * (B * (temp x + d)))

lemma piece_eq (T : Tube G S) (x : ℝ) (V : Config G c) (k : S.Choices) (H : Stores S)
    (F : Forest S.ratio) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen H x F)) (g : ℝ)
    (P : Finset (Rows.In x H F (G:=G))) :
    let C := fog H F T x V k
    let m := meanLog H F T x V k q d Y
    let Q := Rows.gram T x V k (shots S x) H F
    let t := Rows.eta T x V k (shots S x) H F q d Y m g
    into P (C⁻¹-Q) t = piece T x V k H F q d Y g P := by
  intro C m Q t
  funext z
  unfold piece into t Q m C Rows.adjustment quad
  simp only [dotProduct_zero, zero_dotProduct]
  ring

lemma spectral_at {P : Patch} {R : Teller G} {x K σ r b η g₀ : ℝ} {o : ℕ}
    (he : Sky G R P x K r o σ b η g₀) (hK : 0<K) (hσ : 0 ≤ σ) (hr : 0 ≤ r)
    (T : Tube G S) (hP : S.patch=P) (hS : 100*(1+radiusB x) ≤ c.val) (hT : R.Funds S T)
    (V : Config G c) (k : S.Choices) (H : Stores S) (F : Forest S.ratio)
    (hV : H.flags = RG.flags (temp x) V) :
    let C := fog H F T x V k
    let Q := Rows.gram T x V k (shots S x) H F
    C.PosDef ∧ Q.PosDef ∧ Ceiling C K ∧ ∀ z, |quad (C⁻¹-Q) z| ≤ rate (-b) (radiusB x)*K*(z ⬝ᵥ z) := by
  obtain ⟨h1,h2,h3,h4,-⟩ := directly P R he hK S T hP hT hS V k H F hV 0 (by simpa using hr)
  let e := rate (-b) (radiusB x)
  have h := pay_pours h4 (mul_nonneg (rate_pos ..).le hK.le)
  have hh := pay_pours h3 hK.le
  simp only [prism, pilot, Motion.increment_zero, Pi.sub_apply] at h1 h2 h hh
  intro C Q
  refine ⟨h1,h2,fun z => ?_,fun z => ?_⟩
  · have hz := pricedUpper C hσ hh z
    rwa [Schur.sumSq_dot] at hz
  have ht := Schur.estimate (h.weaker hσ le_rfl) z z
  rw [Schur.sumSq_dot] at ht
  unfold quad Q C
  linarith only [ht]

/-- Post-L purchase; `θ` to pay the linear source can be taken even
exponentially shrinking (`ε` displayed), before any V, periods or supports.
Receipt includes the Sky certificate used at Z. Same common witnesses for
every coupling and Y. Uses only branch-patch and `Funds` with the stated size
and V guard, not presupplied hypotheses about the norm/support/PD of the
changed law. No all-period price uniform in g or d independent of their size;
the estimate retains them explicitly! -/
def PatchPrice (G : Gauge) (R : Teller G) (P : Patch) (p : ℝ) (o : ℕ)
    (K M B s b r σ η g₀ : ℝ) (x : ℝ) : Prop :=
  let ε := rate (-b) (radiusB x)*K
  Sky G R P x K r o σ b η g₀ ∧ K*(p*(ε+ε/2)) ≤ 1/4 ∧
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P →
      100*(1+radiusB x) ≤ c.val → R.Funds S T → ∀ (V : Config G c) (k : S.Choices)
      (H : Stores S) (F : Forest S.ratio), H.flags = RG.flags (temp x) V →
      ∀ (q : Chi) (g d θ : ℝ), 0<g → 0<d → 0<θ → K*(p*(θ+ε/2)) ≤ 1/4 →
      ∀ (Y : LinkArray G (Frozen H x F)) (U : Finset (Rows.In x H F (G:=G))),
        book T x V k H F q d Y g U p (intoCost p K ε θ (load x g d M B s) U.card)

lemma error_limit (b : ℝ) (hb : 0<b) : Tendsto (fun x => rate (-b) (radiusB x)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp ((tendsto_natCast_atTop_atTop.comp
    Work.E01.radiusB_tendsto).const_mul_atTop_of_neg (neg_lt_zero.mpr hb))

/-- Produce the exact-type consumer/estimate. No Cosmo/Directed hypotheses
at purchase. Power can be chosen as a parameter BEFORE even the patch. -/
theorem blocks (p : ℝ) (hp : 1 ≤ p) (o : ℕ) (G : Gauge) (P : Patch) (R : Teller G)
    (hP : P.Branches R.bind G) :
    ∃ K M B s b r σ η g₀ : ℝ, 0<K ∧ 0<M ∧ 0 ≤ B ∧ 0<s ∧ 0<b ∧ 0<r ∧ 0<σ ∧ 0<η ∧ 0<g₀ ∧
      ∀ᶠ x in atTop, PatchPrice G R P p o K M B s b r σ η g₀ x := by
  obtain ⟨K,r,σ,b,η,g₀,hK,hr,hσ,hb,hη,hg,he⟩ := fromTeller P G R hP o
  obtain ⟨s,u,M,D,B,hs,_,hM,_,hB,h⟩ := AnalyticBridge.GaussianFieldAlignment.Bias.advanced R P hP
  let ε x := rate (-b) (radiusB x)*K
  have ht : Tendsto ε atTop (𝓝 0) := by simpa using (error_limit b hb).mul_const K
  have hy : Tendsto (fun x => K*(p*(ε x+ε x/2))) atTop (𝓝 0) := by
    simpa using ((ht.add (ht.div_const 2)).const_mul p).const_mul K
  refine ⟨K,M,B,s,b,r,σ,η,g₀,hK,hM,hB,hs,hb,hr,hσ,hη,hg,?_⟩
  filter_upwards [h,he,hy.eventually (eventually_lt_nhds (show 0 < (1/4:ℝ) by norm_num)),
    Work.E01.radiusB_tendsto.eventually_ge_atTop (macroR P)] with x ha hx hi hL
  refine ⟨hx,hi.le,?_⟩
  intro c f S T hS hn hT V k H F hV q g d θ hg hd hθ hU Y U
  have hz : Bid.Larger (G:=G) S := by
    have hc : c.val ≤ f.val := by rw [S.sizes]; exact le_mul_of_one_le_right (Nat.zero_le _) S.patch.L.property
    refine ⟨?_,?_,by omega⟩
    · rw [hS, hT.knobs]; exact hP
    rw [hS]; omega
  obtain ⟨hC,hQ,hw,hj⟩ := spectral_at hx hK hσ.le hr.le T hS hn hT V k H F hV
  obtain ⟨_,_,_,hl,-⟩ := (ha S T hz hS hn hT H F k V hV).2 q d Y hd
  unfold book
  rw [← piece_eq]
  apply insert_letter hC hw hK ((isHermitian_iff_isSymm.mp hC.inv.isHermitian).sub
    (isHermitian_iff_isSymm.mp hQ.isHermitian)) (mul_nonneg (rate_pos ..).le hK.le)
    hj _ hp hθ hU
  let t := Rows.eta T x V k (shots S x) H F q d Y (meanLog H F T x V k q d Y) g
  intro i _
  refine (norm_le_pi_norm t i).trans ?_
  unfold t Rows.eta load
  rw [norm_smul, norm_neg, Real.norm_of_nonneg (inv_pos.mpr hg).le]
  exact mul_le_mul_of_nonneg_left hl (inv_pos.mpr hg).le

section Owners
variable (x : ℝ) (A : Stores S) (F : Forest S.ratio)
  (σ B : ℝ) (hσ : 0 < σ) (U : Finset (Site c))

include hσ




end Owners

end YM.SectorTools.PhysicalGaussianInsertion.Physical
