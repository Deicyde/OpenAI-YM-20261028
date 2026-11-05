import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.PSeries
import YM.MultiNext.VACUUM_STABILITY.Holding.Offers
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Dues
import YM.Next.UV_STRESS.Across
import YM.Push.BETA_TRANSPORT.Comparisons
import YM.Push.COMMON_WITNESSES.Fields
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.PRICE_COMPILER.Suppression
import YM.Push.RELAY_DIFFERENCE.Attaching
import YM.Push.RELAY_DIFFERENCE.TwoSided
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Counting

/-!
Even on the selected non-diagonal covariance/mean, partially release
z into real Haar variables so hard indicators, tags etc can use those group
inputs. The return after deriving uses EXACTLY the original Gaussian at the
evaluation point. No derivative of the window through a branch claimed. The
held chart log is only used inside an actual bijective patch; elsewhere it
has no intended meaning. No independence needed between the two subsets.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ProofPorts.CommonComplexProduction
open Set Function Filter Matrix Lattice RG Wilson Precision Multi.Vacuum Next.SectorChange
open MeasureTheory Gaussian
open scoped Topology BigOperators Classical MatrixOrder
variable {G : Gauge} {I : Type}

structure Pin (G : Gauge) (I : Type) where
  held : Finset I
  chart : ChartRatio G
  g : ℝ

namespace Pin
variable (P : Pin G I)

abbrev Stays := ↥P.held
abbrev Floats := {i : I // i∉P.held}
abbrev Group := LinkArray G P.Stays
abbrev State := Prices G P.Floats × P.Group
abbrev Shift := Prices G P.Stays

variable [Fintype I] [DecidableEq I]

def switch : Prices G I ≃ᵐ Prices G P.Floats × P.Shift := tape.trans <|
  (MeasurableEquiv.piEquivPiSubtypeProd _ (·∈P.held)).trans
    ((MeasurableEquiv.prodCongr tape.symm tape.symm).trans MeasurableEquiv.prodComm)

lemma units : MeasurePreserving P.switch volume volume := by
  have h := measurePreserving_piEquivPiSubtypeProd (α:=fun _ : I => G.Color) (fun _ => volume) (·∈P.held)
  have hd : MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : I => G.Color) (·∈P.held)) volume
      ((volume : Measure (LogArray G P.Stays)).prod (volume : Measure (LogArray G P.Floats))) := by
    convert! h using 2
    show Measure.pi (fun _ : P.Stays => (volume : Measure G.Color)) = _
    congr 1
    exact Subsingleton.elim _ _
  exact Measure.measurePreserving_swap.comp ((tape_volume.symm.prod tape_volume.symm).comp (hd.comp tape_volume))

def basis := volume.prod (piHaar G P.Stays) (α:=Prices G P.Floats)
instance : SFinite P.basis := by unfold basis piHaar; infer_instance

def zone (m : P.Shift) := displaced m P.g

def fetch (m : P.Shift) (v : P.Group) (z : Prices G I) : P.State :=
  ((P.switch z).1, release v (P.zone m (P.switch z).2))

def scan (v : P.Group) : Set P.State := Prod.snd ⁻¹' covered P.chart v

def trace (m : P.Shift) : Set (Prices G I) := {z | P.zone m (P.switch z).2 ∈ mouth P.chart}

def branch (v : P.Group) (y : P.Group) : LogArray G P.Stays := Function.invFunOn (release v) (mouth P.chart) y

def rewind (m : P.Shift) (v : P.Group) (r : P.State) : Prices G I := P.switch.symm
  (r.1,P.g⁻¹ • (tape.symm (P.branch v r.2)-m))

def faceFee (C : Gaussian.Table (I × G.ColorIndex)) (m : P.Shift) (z : Prices G I) : ℝ :=
  if z∈P.trace m then (Gaussian.coat C * Real.exp (force C z/2)) *
     (P.g ^ Fintype.card (P.Stays × G.ColorIndex) * pay P.chart (P.zone m (P.switch z).2)) else 0

def logKernel (C : Gaussian.Table (I × G.ColorIndex)) (m : P.Shift) (v : P.Group) (r : P.State) :=
  -(force C (P.rewind m v r) / 2) - Real.log (Gaussian.coat C) - (∑ j,Real.log (P.chart.J (P.branch v r.2 j)))

def exchangeRate := (P.g ^ Fintype.card (P.Stays × G.ColorIndex) * P.chart.scale ^ Fintype.card P.Stays)⁻¹

def kernel (C : Gaussian.Table (I × G.ColorIndex)) (m : P.Shift) (v : P.Group) (r : P.State) :=
  P.exchangeRate * Real.exp (P.logKernel C m v r)

def pinned (C : Gaussian.Table (I × G.ColorIndex)) (m : P.Shift) (v : P.Group) (f : Prices G I → ℂ) : P.State → ℂ :=
  (P.scan v).indicator fun r => P.kernel C m v r • f (P.rewind m v r)

structure Clean : Prop where
  legal : LocalRatio P.chart
  pos : 0<P.g

omit [Fintype I] [DecidableEq I] in
@[fun_prop] lemma zone_meas (m : P.Shift) : Measurable (P.zone m) := by
  apply tape.measurable.comp (by fun_prop : Measurable (fun z => m + P.g • z))
lemma trace_meas (m : P.Shift) : MeasurableSet (P.trace m) := ((P.zone_meas m).comp (measurable_snd.comp P.switch.measurable)) (mouth_meas _)
lemma fetch_meas (m : P.Shift) (v : P.Group) : Measurable (P.fetch m v) := (measurable_fst.comp P.switch.measurable).prodMk
    ((release_continuous v).measurable.comp ((P.zone_meas m).comp (measurable_snd.comp P.switch.measurable)))

namespace Clean
variable {P} {C : Gaussian.Table (I × G.ColorIndex)} (h : P.Clean) (hC : C.PosDef) {m : P.Shift} {v : P.Group} {z : Prices G I}

include h in
omit [Fintype I] [DecidableEq I] in
lemma chart_pos {a : LogArray G P.Stays} (h' : a ∈ mouth P.chart) : 0 < pay P.chart a :=
  Finset.prod_pos fun i _ => mul_pos h.legal.scale (h.legal.pos _ (h' i (Set.mem_univ _)))
include hC h in
lemma coins_pos (m : P.Shift) (z : Prices G I) : 0 ≤ P.faceFee C m z := by
  unfold faceFee; split; rename_i he
  · have hp := h.pos
    exact mul_nonneg (mul_nonneg (coat_pos hC).le (Real.exp_pos _).le) (by have hh := h.chart_pos he; positivity)
  rfl

include h in
lemma kernel_pos (m : P.Shift) (v : P.Group) (r : P.State) : 0 < P.kernel C m v r := by
  have hp := h.pos; have hh := h.legal.scale; unfold kernel exchangeRate; positivity

lemma seen_inside (v : P.Group) (he : z∈P.trace m) : P.fetch m v z ∈ P.scan v := by
  intro i _
  let y := P.zone m (P.switch z).2
  exact ⟨G.lieExp (y i),⟨y i,he i (Set.mem_univ i),rfl⟩,rfl⟩

include h in
lemma scanned (v : P.Group) (he : z∈P.trace m) : P.branch v (P.fetch m v z).2 = P.zone m (P.switch z).2 :=
  (release_injOn h.legal v).leftInvOn_invFunOn he

include h in
lemma unwinds (v : P.Group) (he : z∈P.trace m) : P.rewind m v (P.fetch m v z) = z := by
  unfold rewind; rw [h.scanned v he]; simp [zone,displaced,h.pos.ne',fetch]

include hC h in
lemma reimbursed (v : P.Group) (he : z∈P.trace m) : P.faceFee C m z * P.kernel C m v (P.fetch m v z)=1 := by
  let y := P.zone m (P.switch z).2
  have hh (i : P.Stays) : 0<P.chart.J (y i) := h.legal.pos _ (he i (Set.mem_univ i))
  rw [kernel,faceFee,logKernel, if_pos he,h.scanned v he, h.unwinds v he,Real.exp_sub,Real.exp_sub,Real.exp_neg,
    Real.exp_log (Gaussian.coat_pos hC),Real.exp_sum]; unfold exchangeRate
  change Gaussian.coat C * Real.exp _ * (_ * pay P.chart y) * (_ * (_ / (∏ i,Real.exp (Real.log (P.chart.J (y i))))))=1
  simp_rw [Real.exp_log (hh _),pay,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]
  have hp := h.pos; have hv := h.legal.scale; have hi := Gaussian.coat_pos hC
  have hj := Finset.prod_pos (s:=Finset.univ) fun i _=>hh i
  field_simp

include h in
lemma fee_meas (m : P.Shift) : Measurable (P.faceFee C m) := by
  have hf : Measurable (fun z : Prices G I => force C z) := by unfold force mulVec dotProduct; fun_prop
  have hw:= (pay_meas h.legal (ι:=P.Stays)).comp ((P.zone_meas m).comp (measurable_snd.comp P.switch.measurable))
  exact Measurable.ite (P.trace_meas m) ((measurable_const.mul ((hf.div_const _).exp)).mul (measurable_const.mul hw)) measurable_const
end Clean
end Pin
end YM.ProofPorts.CommonComplexProduction
